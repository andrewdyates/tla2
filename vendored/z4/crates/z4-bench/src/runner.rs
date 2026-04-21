// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eval runner: discovers evals from the YAML registry, executes benchmarks
//! natively in Rust, and applies competition-standard scoring.

use anyhow::{bail, Context, Result};
use std::path::{Path, PathBuf};

use crate::scoring::{self, Competition, ResultsFile};

// ===================================================================
// Eval registry
// ===================================================================

/// Minimal YAML eval spec — we only need a few fields.
#[derive(Debug)]
struct EvalSpec {
    id: Option<String>,
    inputs: Option<EvalInputs>,
}

#[derive(Debug)]
struct EvalInputs {
    timeout_sec: Option<f64>,
    benchmarks_dir: Option<String>,
    /// Text file listing benchmark paths, one per line (e.g., SAT heldout set).
    list_file: Option<String>,
    /// Set manifest file relative to benchmarks_dir (e.g., CHC-COMP LIA.set).
    set_file: Option<String>,
    /// Number of runs per benchmark for statistical reliability.
    runs: Option<u32>,
    /// Subdirectories to scope discovery to (e.g., QF_BV, QF_LIA).
    suite_dirs: Option<Vec<String>>,
    /// Reference solver binary name for comparison (e.g., "z3").
    reference_solver: Option<String>,
}

fn repo_root() -> PathBuf {
    let mut dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    loop {
        if dir.join("Cargo.toml").exists() && dir.join("evals").exists() {
            return dir;
        }
        if !dir.pop() {
            return std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        }
    }
}

fn registry_dir() -> PathBuf {
    repo_root().join("evals").join("registry")
}

fn discover_evals() -> Result<Vec<(String, EvalSpec)>> {
    let dir = registry_dir();
    if !dir.exists() {
        bail!("eval registry not found: {}", dir.display());
    }

    let mut evals = Vec::new();
    for entry in std::fs::read_dir(&dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("yaml") {
            continue;
        }
        let text = std::fs::read_to_string(&path)
            .with_context(|| format!("reading {}", path.display()))?;
        let spec = parse_eval_spec_minimal(&text, &path)?;
        let eval_id = spec
            .id
            .clone()
            .unwrap_or_else(|| {
                path.file_stem()
                    .unwrap_or_default()
                    .to_string_lossy()
                    .to_string()
            });
        evals.push((eval_id, spec));
    }
    evals.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(evals)
}

/// Minimal YAML parser — extracts only the fields we need without a yaml dependency.
fn parse_eval_spec_minimal(text: &str, path: &Path) -> Result<EvalSpec> {
    let mut id = None;
    let mut timeout_sec = None;
    let mut benchmarks_dir = None;
    let mut list_file = None;
    let mut set_file = None;
    let mut runs = None;
    let mut reference_solver = None;
    let mut suite_dirs: Option<Vec<String>> = None;
    let mut in_suite_dirs = false;

    for line in text.lines() {
        let trimmed = line.trim();

        // Collect suite_dirs list items (YAML list under suite_dirs:)
        if in_suite_dirs {
            if let Some(item) = trimmed.strip_prefix("- ") {
                suite_dirs
                    .get_or_insert_with(Vec::new)
                    .push(strip_yaml_value(item));
                continue;
            } else {
                in_suite_dirs = false;
            }
        }

        if let Some(rest) = trimmed.strip_prefix("id:") {
            id = Some(strip_yaml_value(rest));
        } else if let Some(rest) = trimmed.strip_prefix("timeout_sec:") {
            timeout_sec = strip_yaml_value(rest).parse::<f64>().ok();
        } else if let Some(rest) = trimmed.strip_prefix("benchmarks_dir:") {
            benchmarks_dir = Some(strip_yaml_value(rest));
        } else if let Some(rest) = trimmed.strip_prefix("list_file:") {
            list_file = Some(strip_yaml_value(rest));
        } else if let Some(rest) = trimmed.strip_prefix("set_file:") {
            set_file = Some(strip_yaml_value(rest));
        } else if let Some(rest) = trimmed.strip_prefix("runs:") {
            runs = strip_yaml_value(rest).parse::<u32>().ok();
        } else if let Some(rest) = trimmed.strip_prefix("reference_solver:") {
            reference_solver = Some(strip_yaml_value(rest));
        } else if trimmed == "suite_dirs:" {
            in_suite_dirs = true;
            suite_dirs = Some(Vec::new());
        }
    }

    if id.is_none() {
        id = Some(
            path.file_stem()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string(),
        );
    }

    Ok(EvalSpec {
        id,
        inputs: Some(EvalInputs {
            timeout_sec,
            benchmarks_dir,
            list_file,
            set_file,
            runs,
            suite_dirs,
            reference_solver,
        }),
    })
}

/// Find a solver binary by name, checking PATH.
fn find_solver(name: &str) -> Option<PathBuf> {
    // Try the name directly (which checks)
    let output = std::process::Command::new("which")
        .arg(name)
        .output()
        .ok()?;
    if output.status.success() {
        let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
        if !path.is_empty() {
            return Some(PathBuf::from(path));
        }
    }
    None
}

/// Infer competition domain from eval ID prefix.
fn infer_domain(eval_id: &str) -> &str {
    if eval_id.starts_with("sat-") {
        "sat"
    } else if eval_id.starts_with("smt-") {
        "smt"
    } else if eval_id.starts_with("chccomp-") || eval_id.starts_with("chc-") {
        "chc"
    } else {
        "unknown"
    }
}

fn infer_competition(eval_id: &str) -> Competition {
    match infer_domain(eval_id) {
        "sat" => Competition::SatComp,
        "smt" => Competition::SmtComp,
        "chc" => Competition::ChcComp,
        _ => Competition::SmtComp,
    }
}

fn infer_division(eval_id: &str) -> String {
    if let Some(suffix) = eval_id.strip_prefix("smt-smtcomp-") {
        suffix.to_uppercase().replace('-', "_")
    } else if let Some(suffix) = eval_id.strip_prefix("smt-local-") {
        if suffix == "suite" {
            "mixed".to_string()
        } else {
            suffix.to_uppercase().replace('-', "_")
        }
    } else {
        "unknown".to_string()
    }
}

fn infer_track(eval_id: &str) -> String {
    if eval_id.contains("extra-small-lia") {
        "LIA-extra-small".to_string()
    } else if eval_id.contains("lia-lin") {
        "LIA-Lin".to_string()
    } else if eval_id.contains("lia") {
        "LIA".to_string()
    } else {
        "unknown".to_string()
    }
}

fn competition_timeout(eval_id: &str) -> f64 {
    infer_competition(eval_id).standard_timeout()
}

// ===================================================================
// Eval execution
// ===================================================================

pub struct RunArgs {
    pub eval_ids: Vec<String>,
    pub all: bool,
    pub domain: Option<String>,
    pub competition: bool,
    pub z4: PathBuf,
    pub timeout: Option<f64>,
    pub output: Option<PathBuf>,
    /// CLI override for number of runs per benchmark (1 = no override, use YAML).
    pub runs: u32,
    /// CLI override for reference solver binary path.
    pub reference_solver: Option<PathBuf>,
    pub quiet: bool,
}

/// Score an existing results file and print the result.
fn score_and_print(
    results_path: &Path,
    eval_id: &str,
    timeout: f64,
    competition_mode: bool,
) -> Result<serde_json::Value> {
    let data = ResultsFile::load(results_path)?;
    let items = data.items();
    let mode = if competition_mode {
        "competition"
    } else {
        "dev"
    };
    let comp = infer_competition(eval_id);

    match comp {
        Competition::SatComp => {
            let score = scoring::score_sat(items, timeout);
            println!("  [{mode}, T={timeout:.0}s] {score}");
            Ok(serde_json::to_value(&score)?)
        }
        Competition::SmtComp => {
            let div = infer_division(eval_id);
            let score = scoring::score_smt(items, timeout, &div);
            println!("  [{mode}, T={timeout:.0}s] {score}");
            Ok(serde_json::to_value(&score)?)
        }
        Competition::ChcComp => {
            let track = infer_track(eval_id);
            let score = scoring::score_chc(items, timeout, &track);
            println!("  [{mode}, T={timeout:.0}s] {score}");
            Ok(serde_json::to_value(&score)?)
        }
    }
}

fn run_single_eval(
    eval_id: &str,
    spec: &EvalSpec,
    args: &RunArgs,
) -> Result<serde_json::Value> {
    let inputs = spec.inputs.as_ref();

    // Determine timeout
    let timeout = if let Some(t) = args.timeout {
        t
    } else if args.competition {
        competition_timeout(eval_id)
    } else {
        inputs.and_then(|i| i.timeout_sec).unwrap_or(60.0)
    };

    let mode_label = if args.competition {
        "COMPETITION"
    } else {
        "dev"
    };

    if !args.quiet {
        eprintln!();
        eprintln!("{}", "=".repeat(60));
        eprintln!("[{eval_id}] mode={mode_label} timeout={timeout:.0}s");
        eprintln!("{}", "=".repeat(60));
    }

    let root = repo_root();
    let domain = infer_domain(eval_id);

    // Determine benchmarks_dir from spec or infer from domain
    let benchmarks_dir = spec
        .inputs
        .as_ref()
        .and_then(|i| i.benchmarks_dir.as_deref())
        .map(|d| root.join(d))
        .unwrap_or_else(|| root.join("benchmarks").join(domain));

    let z4_path = if args.z4.is_relative() {
        root.join(&args.z4)
    } else {
        args.z4.clone()
    };

    // Build explicit file list from list_file, set_file, or suite_dirs
    let file_list = build_file_list(spec, &root, &benchmarks_dir)?
        .or_else(|| build_suite_dirs_list(spec, &benchmarks_dir, domain));

    // Determine number of runs: CLI --runs overrides YAML spec (CLI default 1 = use YAML)
    let runs = if args.runs > 1 {
        args.runs
    } else {
        inputs.and_then(|i| i.runs).unwrap_or(1).max(1)
    };

    // Resolve reference solver: CLI --reference-solver overrides YAML spec
    let ref_solver = if let Some(ref cli_solver) = args.reference_solver {
        Some(cli_solver.clone())
    } else {
        inputs
            .and_then(|i| i.reference_solver.as_deref())
            .and_then(find_solver)
    };

    let native_args = crate::native::NativeRunArgs {
        z4: &z4_path,
        benchmarks_dir: &benchmarks_dir,
        timeout_sec: timeout,
        domain,
        quiet: args.quiet,
        file_list,
        runs,
        reference_solver: ref_solver,
    };

    let results = crate::native::run_native(&native_args)?;

    // Print comparison summary if reference solver was used
    if let Some(ref summary) = results.comparison {
        if !args.quiet {
            eprintln!();
            eprintln!("[{eval_id}] comparison vs {}", summary.reference_solver);
            eprintln!(
                "  agree={} disagree={} z4_only={} ref_only={}",
                summary.agree, summary.disagree, summary.z4_only, summary.ref_only,
            );
            if summary.both_solved > 0 {
                eprintln!(
                    "  both_solved={}: z4_faster={} ref_faster={} z4_total={:.1}s ref_total={:.1}s",
                    summary.both_solved,
                    summary.z4_faster,
                    summary.ref_faster,
                    summary.z4_total_time,
                    summary.ref_total_time,
                );
            }
        }
    }

    // Write results.json in the standard location
    let run_id = results.environment.timestamp.replace(':', "-");
    let output_dir = root
        .join("evals")
        .join("results")
        .join(eval_id)
        .join(&run_id);
    std::fs::create_dir_all(&output_dir)?;

    let results_path = output_dir.join("results.json");
    let json = serde_json::to_string_pretty(&results)?;
    std::fs::write(&results_path, &json)?;

    if !args.quiet {
        eprintln!("[{eval_id}] results written to {}", results_path.display());
    }

    // Score the results
    score_and_print(&results_path, eval_id, timeout, args.competition)
}

pub fn cmd_run(args: RunArgs) -> Result<()> {
    let evals = discover_evals()?;
    if evals.is_empty() {
        bail!("no eval specs found in evals/registry/");
    }

    // Determine which evals to run
    let selected: Vec<(String, EvalSpec)> = if args.all {
        evals
    } else if let Some(ref domain) = args.domain {
        evals
            .into_iter()
            .filter(|(id, _)| infer_domain(id) == domain.as_str())
            .collect()
    } else if !args.eval_ids.is_empty() {
        let available: Vec<String> = evals.iter().map(|(id, _)| id.clone()).collect();
        for id in &args.eval_ids {
            if !available.contains(id) {
                bail!(
                    "unknown eval: {id}\navailable: {}",
                    available.join(", ")
                );
            }
        }
        evals
            .into_iter()
            .filter(|(id, _)| args.eval_ids.contains(id))
            .collect()
    } else {
        bail!("specify eval IDs, --all, or --domain {{sat,smt,chc}}");
    };

    if selected.is_empty() {
        bail!("no matching evals found");
    }

    // Check Z4 binary
    let z4_path = if args.z4.is_relative() {
        repo_root().join(&args.z4)
    } else {
        args.z4.clone()
    };
    if !z4_path.exists() {
        bail!(
            "Z4 binary not found: {}\nBuild first: cargo build --release -p z4",
            z4_path.display()
        );
    }

    let mut all_scores = Vec::new();

    for (eval_id, spec) in &selected {
        match run_single_eval(eval_id, spec, &args) {
            Ok(score) => all_scores.push(serde_json::json!({
                "eval_id": eval_id,
                "competition": infer_competition(eval_id).name(),
                "score": score,
            })),
            Err(e) => {
                eprintln!("[{eval_id}] error: {e:#}");
                all_scores.push(serde_json::json!({
                    "eval_id": eval_id,
                    "error": format!("{e:#}"),
                }));
            }
        }
    }

    // Print scorecard
    let mode = if args.competition {
        "competition-standard timeouts"
    } else {
        "dev timeouts"
    };
    println!();
    println!("{}", "=".repeat(60));
    println!("SCORECARD ({mode})");
    println!("{}", "=".repeat(60));
    println!("Scores printed above per eval.");

    // Write combined output
    if let Some(ref output_path) = args.output {
        let env = crate::environment::Environment::capture(&z4_path);
        let scorecard = serde_json::json!({
            "environment": env,
            "mode": if args.competition { "competition" } else { "dev" },
            "results": all_scores,
        });
        if let Some(parent) = output_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(output_path, serde_json::to_string_pretty(&scorecard)?)?;
        println!("Scorecard written to: {}", output_path.display());
    }

    Ok(())
}

// ===================================================================
// list command
// ===================================================================

pub fn cmd_list() -> Result<()> {
    let evals = discover_evals()?;
    if evals.is_empty() {
        println!("No evals found in evals/registry/");
        return Ok(());
    }

    println!(
        "{:<40} {:<8} {:<12} {:<10} {:<12}",
        "Eval ID", "Domain", "Scoring", "Timeout", "Std Timeout"
    );
    println!("{}", "-".repeat(90));

    for (eval_id, spec) in &evals {
        let domain = infer_domain(eval_id);
        let comp = infer_competition(eval_id);
        let dev_timeout = spec
            .inputs
            .as_ref()
            .and_then(|i| i.timeout_sec)
            .map(|t| format!("{t:.0}s"))
            .unwrap_or_else(|| "?".to_string());
        let std_timeout = format!("{:.0}s", comp.standard_timeout());

        println!(
            "{:<40} {:<8} {:<12} {:<10} {:<12}",
            eval_id,
            domain,
            comp.name(),
            dev_timeout,
            std_timeout,
        );
    }

    Ok(())
}

// ===================================================================
// Helpers
// ===================================================================

/// Build an explicit benchmark file list from list_file or set_file.
///
/// - `list_file`: text file with one path per line (relative to repo root).
///   Lines starting with `#` or empty are skipped. Optional second column
///   is ignored (used for expected result in some formats).
/// - `set_file`: manifest relative to benchmarks_dir, listing paths relative
///   to benchmarks_dir. Lines ending in `.yml` are converted to `.smt2`.
///
/// Returns `None` if neither is specified (caller uses directory discovery).
fn build_file_list(
    spec: &EvalSpec,
    root: &Path,
    benchmarks_dir: &Path,
) -> Result<Option<Vec<PathBuf>>> {
    let inputs = match spec.inputs.as_ref() {
        Some(i) => i,
        None => return Ok(None),
    };

    if let Some(ref list_path) = inputs.list_file {
        let path = root.join(list_path);
        let text = std::fs::read_to_string(&path)
            .with_context(|| format!("reading list_file {}", path.display()))?;
        let mut files = Vec::new();
        let mut total = 0u32;
        let mut missing = 0u32;
        for line in text.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            total += 1;
            // First column is the path, rest is optional metadata
            let file_path = trimmed.split_whitespace().next().unwrap();
            let full = root.join(file_path);
            if full.exists() {
                files.push(full);
            } else {
                missing += 1;
            }
        }
        if missing > 0 {
            eprintln!(
                "warning: list_file {}: {missing}/{total} benchmarks not found on disk",
                list_path
            );
        }
        files.sort();
        return Ok(Some(files));
    }

    if let Some(ref set_name) = inputs.set_file {
        let set_path = benchmarks_dir.join(set_name);
        let text = std::fs::read_to_string(&set_path)
            .with_context(|| format!("reading set_file {}", set_path.display()))?;
        let mut files = Vec::new();
        let mut total = 0u32;
        let mut missing = 0u32;
        for line in text.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            total += 1;
            // CHC-COMP set files list .yml paths; convert to .smt2
            let smt2_name = if trimmed.ends_with(".yml") {
                trimmed.replace(".yml", ".smt2")
            } else {
                trimmed.to_string()
            };
            let full = benchmarks_dir.join(&smt2_name);
            if full.exists() {
                files.push(full);
            } else {
                missing += 1;
            }
        }
        if missing > 0 {
            eprintln!(
                "warning: set_file {}: {missing}/{total} benchmarks not found on disk",
                set_name
            );
        }
        files.sort();
        return Ok(Some(files));
    }

    Ok(None)
}

/// Build file list from suite_dirs — discover benchmarks from listed subdirectories only.
fn build_suite_dirs_list(
    spec: &EvalSpec,
    benchmarks_dir: &Path,
    domain: &str,
) -> Option<Vec<PathBuf>> {
    let dirs = spec.inputs.as_ref()?.suite_dirs.as_ref()?;
    if dirs.is_empty() {
        return None;
    }
    let mut files = Vec::new();
    for subdir in dirs {
        let path = benchmarks_dir.join(subdir);
        if path.is_dir() {
            if let Ok(discovered) = crate::native::discover_benchmarks(&path, domain) {
                files.extend(discovered);
            }
        } else {
            eprintln!("warning: suite_dirs entry not found: {}", path.display());
        }
    }
    files.sort();
    Some(files)
}

/// Strip YAML quoting and inline comments from a value string.
fn strip_yaml_value(raw: &str) -> String {
    let trimmed = raw.trim();
    // Strip inline comment (# preceded by whitespace)
    let no_comment = trimmed
        .find(" #")
        .map(|i| &trimmed[..i])
        .unwrap_or(trimmed)
        .trim();
    // Strip surrounding quotes
    if (no_comment.starts_with('"') && no_comment.ends_with('"'))
        || (no_comment.starts_with('\'') && no_comment.ends_with('\''))
    {
        no_comment[1..no_comment.len() - 1].to_string()
    } else {
        no_comment.to_string()
    }
}

// ===================================================================
// Tests
// ===================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_infer_domain() {
        assert_eq!(infer_domain("sat-par2-dev"), "sat");
        assert_eq!(infer_domain("smt-smtcomp-qf-lia"), "smt");
        assert_eq!(infer_domain("smt-local-suite"), "smt");
        assert_eq!(infer_domain("chccomp-2025-lia"), "chc");
        assert_eq!(infer_domain("chc-something"), "chc");
        assert_eq!(infer_domain("other"), "unknown");
    }

    #[test]
    fn test_infer_competition() {
        assert_eq!(infer_competition("sat-par2-dev"), Competition::SatComp);
        assert_eq!(infer_competition("smt-local-suite"), Competition::SmtComp);
        assert_eq!(infer_competition("chccomp-2025-lia"), Competition::ChcComp);
        assert_eq!(infer_competition("unknown-eval"), Competition::SmtComp);
    }

    #[test]
    fn test_infer_division() {
        assert_eq!(infer_division("smt-smtcomp-qf-lia"), "QF_LIA");
        assert_eq!(infer_division("smt-smtcomp-qf-bv"), "QF_BV");
        assert_eq!(infer_division("smt-local-suite"), "mixed");
        assert_eq!(infer_division("smt-local-qf-lia"), "QF_LIA");
        assert_eq!(infer_division("chccomp-2025-lia"), "unknown");
    }

    #[test]
    fn test_infer_track() {
        assert_eq!(
            infer_track("chccomp-2025-extra-small-lia"),
            "LIA-extra-small"
        );
        assert_eq!(infer_track("chccomp-2025-lia-lin"), "LIA-Lin");
        assert_eq!(infer_track("chccomp-2025-lia"), "LIA");
        assert_eq!(infer_track("sat-par2-dev"), "unknown");
    }

    #[test]
    fn test_strip_yaml_value() {
        assert_eq!(strip_yaml_value(" hello "), "hello");
        assert_eq!(strip_yaml_value(" \"quoted\" "), "quoted");
        assert_eq!(strip_yaml_value(" 'single' "), "single");
        assert_eq!(strip_yaml_value(" 60 # seconds "), "60");
        assert_eq!(strip_yaml_value(" value#nospace "), "value#nospace");
    }

    #[test]
    fn test_parse_eval_spec_minimal() {
        let yaml = "\
id: sat-par2-dev
version: 1
inputs:
  timeout_sec: 20
  benchmarks_dir: benchmarks/sat/sample
";
        let spec =
            parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.id.as_deref(), Some("sat-par2-dev"));
        let inputs = spec.inputs.unwrap();
        assert_eq!(inputs.timeout_sec, Some(20.0));
        assert_eq!(
            inputs.benchmarks_dir.as_deref(),
            Some("benchmarks/sat/sample")
        );
    }

    #[test]
    fn test_parse_eval_spec_quoted_id() {
        let yaml = "id: \"my-eval\"\ntimeout_sec: 30\n";
        let spec =
            parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.id.as_deref(), Some("my-eval"));
    }

    #[test]
    fn test_parse_eval_spec_inline_comment() {
        let yaml = "id: eval1\ntimeout_sec: 60 # seconds\n";
        let spec =
            parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.inputs.unwrap().timeout_sec, Some(60.0));
    }

    #[test]
    fn test_parse_eval_spec_fallback_id() {
        let yaml = "timeout_sec: 10\n";
        let spec = parse_eval_spec_minimal(
            yaml,
            Path::new("/evals/registry/my-eval.yaml"),
        )
        .unwrap();
        assert_eq!(spec.id.as_deref(), Some("my-eval"));
    }

    #[test]
    fn test_parse_eval_spec_runs() {
        let yaml = "id: test\nruns: 3\ntimeout_sec: 20\n";
        let spec =
            parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.inputs.unwrap().runs, Some(3));
    }

    #[test]
    fn test_parse_eval_spec_suite_dirs() {
        let yaml = "\
id: smt-local-suite
inputs:
  benchmarks_dir: benchmarks/smt/
  suite_dirs:
    - QF_BV
    - QF_LIA
    - QF_LRA
  timeout_sec: 30
";
        let spec =
            parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        let inputs = spec.inputs.unwrap();
        let dirs = inputs.suite_dirs.unwrap();
        assert_eq!(dirs, vec!["QF_BV", "QF_LIA", "QF_LRA"]);
    }

    #[test]
    fn test_parse_eval_spec_reference_solver() {
        let yaml = "id: sat-par2-dev\nreference_solver: z3\ntimeout_sec: 20\n";
        let spec =
            parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(
            spec.inputs.unwrap().reference_solver.as_deref(),
            Some("z3")
        );
    }

    #[test]
    fn test_select_representative_single() {
        let item = crate::native::NativeResultItem {
            file: "test.cnf".to_string(),
            expected: None,
            result: "sat".to_string(),
            time_sec: 1.5,
            cpu_time_sec: 1.5,
            exit_code: Some(10),
        };
        let rep = crate::native::select_representative(vec![item]);
        assert_eq!(rep.time_sec, 1.5);
    }

    #[test]
    fn test_select_representative_median() {
        let make = |t: f64| crate::native::NativeResultItem {
            file: "test.cnf".to_string(),
            expected: None,
            result: "sat".to_string(),
            time_sec: t,
            cpu_time_sec: t,
            exit_code: Some(10),
        };
        // 3 runs: 1.0, 3.0, 2.0 — median is 2.0
        let rep = crate::native::select_representative(vec![
            make(1.0),
            make(3.0),
            make(2.0),
        ]);
        assert_eq!(rep.time_sec, 2.0);
    }
}
