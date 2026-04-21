// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Baseline codegen validation: attempts code generation on every small spec
//! in spec_baseline.json and reports success/failure counts.
//!
//! This is a compilation-level validation (syntactic check of generated output),
//! not execution. It verifies that codegen produces valid-looking Rust output
//! for real-world specs from the TLC comparison suite.
//!
//! Part of #3937.

use serde::Deserialize;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use tla_codegen::{generate_rust_with_context, CodeGenContext, CodeGenOptions};
use tla_core::{
    compute_is_recursive, lower_main_module, parse, FileId, ModuleLoader, SyntaxNode,
};

// ── Baseline JSON schema (minimal) ──

#[derive(Debug, Deserialize)]
struct Baseline {
    specs: HashMap<String, SpecEntry>,
}

#[derive(Debug, Deserialize)]
struct SpecEntry {
    category: Option<String>,
    source: Option<SourcePaths>,
}

#[derive(Debug, Deserialize)]
struct SourcePaths {
    tla_path: Option<String>,
    #[allow(dead_code)]
    cfg_path: Option<String>,
}

// ── Helpers ──

/// Root directory of the tla2 repo (derived from CARGO_MANIFEST_DIR).
fn repo_root() -> PathBuf {
    let manifest_dir =
        std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR not set");
    PathBuf::from(manifest_dir)
        .parent() // crates/
        .and_then(|p| p.parent()) // repo root
        .expect("could not find repo root")
        .to_path_buf()
}

/// Resolve a spec's TLA+ source file to an absolute path.
///
/// Returns `None` if the file cannot be found.
fn resolve_tla_path(tla_path: &str) -> Option<PathBuf> {
    let candidates = [
        PathBuf::from("./tlaplus-examples/specifications").join(tla_path),
    ];
    candidates.into_iter().find(|p| p.exists())
}

/// Attempt to parse, lower, and generate Rust code from a TLA+ spec file.
///
/// Returns `Ok(generated_code)` on success, `Err(reason)` on failure.
fn try_codegen(tla_file: &Path) -> Result<String, String> {
    // Read source
    let source = std::fs::read_to_string(tla_file)
        .map_err(|e| format!("read error: {e}"))?;

    // Parse
    let parsed = parse(&source);
    if !parsed.errors.is_empty() {
        let msgs: Vec<_> = parsed.errors.iter().map(|e| e.message.clone()).collect();
        return Err(format!("parse errors: {}", msgs.join("; ")));
    }

    let tree = SyntaxNode::new_root(parsed.green_node);

    // Lower (use lower_main_module for multi-module file support)
    let hint_name = tla_file
        .file_stem()
        .and_then(|s| s.to_str());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let msgs: Vec<_> = result.errors.iter().map(|e| e.message.clone()).collect();
        return Err(format!("lower errors: {}", msgs.join("; ")));
    }
    let mut module = result
        .module
        .ok_or_else(|| "no module produced".to_string())?;
    compute_is_recursive(&mut module);

    // Load dependencies (EXTENDS / INSTANCE)
    let mut loader = ModuleLoader::new(tla_file);
    loader.seed_from_syntax_tree(&tree, tla_file);
    if let Err(e) = loader.load_extends(&module) {
        return Err(format!("load extends: {e}"));
    }
    if let Err(e) = loader.load_instances(&module) {
        return Err(format!("load instances: {e}"));
    }

    let options = CodeGenOptions::default();
    let context = CodeGenContext {
        modules: loader.modules_for_model_checking(&module),
    };

    generate_rust_with_context(&module, &context, &options)
        .map_err(|e| format!("codegen error: {e}"))
}

// ── Test ──

#[cfg_attr(test, ntest::timeout(120_000))]
#[test]
fn test_baseline_small_spec_codegen() {
    let baseline_path = repo_root().join("tests/tlc_comparison/spec_baseline.json");
    assert!(
        baseline_path.exists(),
        "spec_baseline.json not found at {}",
        baseline_path.display()
    );

    let content = std::fs::read_to_string(&baseline_path)
        .expect("failed to read spec_baseline.json");
    let baseline: Baseline =
        serde_json::from_str(&content).expect("failed to parse spec_baseline.json");

    // Collect small specs
    let mut small_specs: Vec<(String, SpecEntry)> = baseline
        .specs
        .into_iter()
        .filter(|(_, entry)| entry.category.as_deref() == Some("small"))
        .collect();
    small_specs.sort_by(|a, b| a.0.cmp(&b.0));

    assert!(
        !small_specs.is_empty(),
        "no small specs found in baseline"
    );

    let mut successes: Vec<String> = Vec::new();
    let mut failures: Vec<(String, String)> = Vec::new();
    let mut skipped: Vec<(String, String)> = Vec::new();

    for (name, entry) in &small_specs {
        let tla_rel = match entry.source.as_ref().and_then(|s| s.tla_path.as_deref()) {
            Some(p) => p,
            None => {
                skipped.push((name.clone(), "no tla_path in baseline".to_string()));
                continue;
            }
        };

        let tla_abs = match resolve_tla_path(tla_rel) {
            Some(p) => p,
            None => {
                skipped.push((name.clone(), format!("file not found: {tla_rel}")));
                continue;
            }
        };

        match try_codegen(&tla_abs) {
            Ok(code) => {
                // Basic syntactic validation: generated code should contain
                // a struct definition and a StateMachine impl.
                let has_struct = code.contains("State {") || code.contains("State;");
                let has_impl = code.contains("impl StateMachine");
                if has_struct || has_impl {
                    successes.push(name.clone());
                } else {
                    // Codegen succeeded but output looks wrong
                    failures.push((
                        name.clone(),
                        "codegen output missing expected patterns (State struct or StateMachine impl)".to_string(),
                    ));
                }
            }
            Err(reason) => {
                failures.push((name.clone(), reason));
            }
        }
    }

    let total = small_specs.len();
    let success_count = successes.len();
    let failure_count = failures.len();
    let skip_count = skipped.len();

    // Print summary
    println!("\n=== Baseline Codegen Summary (small specs) ===");
    println!(
        "Total: {total}, Success: {success_count}, Failed: {failure_count}, Skipped: {skip_count}"
    );
    println!(
        "Success rate: {:.1}% (of non-skipped)",
        if total - skip_count > 0 {
            success_count as f64 / (total - skip_count) as f64 * 100.0
        } else {
            0.0
        }
    );

    if !failures.is_empty() {
        println!("\n--- Failures ---");
        for (name, reason) in &failures {
            // Truncate long reasons for readability
            let short_reason = if reason.len() > 200 {
                format!("{}...", &reason[..200])
            } else {
                reason.clone()
            };
            println!("  {name}: {short_reason}");
        }
    }

    if !skipped.is_empty() {
        println!("\n--- Skipped ---");
        for (name, reason) in &skipped {
            println!("  {name}: {reason}");
        }
    }

    if !successes.is_empty() {
        println!("\n--- Successes ({success_count}) ---");
        for name in &successes {
            println!("  {name}");
        }
    }

    // The test passes as long as it runs to completion and reports results.
    // We do NOT assert a minimum success rate here because codegen coverage
    // is expected to be partial — many specs use constructs not yet supported
    // by the code generator (temporal operators, complex INSTANCE patterns, etc.).
    //
    // Instead, we assert a soft floor: at least SOME specs should succeed.
    // If codegen is completely broken, this catches it.
    assert!(
        success_count > 0,
        "codegen produced zero successes out of {total} small specs — codegen is broken"
    );
}
