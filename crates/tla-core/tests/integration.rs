// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for parsing and lowering checked-in TLA+ fixtures.

use std::path::{Path, PathBuf};
use tla_core::{lower, parse, parse_to_syntax_tree, resolve, FileId, ResolveErrorKind};

/// Parse a specific TLA+ file.
fn parse_file(path: &Path) -> (bool, Vec<String>) {
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => return (false, vec![format!("Failed to read file: {}", e)]),
    };

    let result = parse(&source);
    let mut issues = Vec::new();

    if !result.errors.is_empty() {
        for err in &result.errors {
            issues.push(format!(
                "Parse error at {}-{}: {}",
                err.start, err.end, err.message
            ));
        }
    }

    (result.errors.is_empty(), issues)
}

/// Run parse + lower for one TLA+ file.
fn parse_and_lower(path: &Path) -> (bool, Vec<String>) {
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => return (false, vec![format!("Failed to read file: {}", e)]),
    };

    let result = parse(&source);
    let mut issues = Vec::new();

    if !result.errors.is_empty() {
        for err in &result.errors {
            issues.push(format!("Parse error: {}", err.message));
        }
        return (false, issues);
    }

    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(FileId(0), &tree);

    if !lower_result.errors.is_empty() {
        for err in &lower_result.errors {
            issues.push(format!("Lowering error: {err:?}"));
        }
        return (false, issues);
    }

    if lower_result.module.is_none() {
        issues.push("Lowering produced no module".to_string());
        return (false, issues);
    }

    (true, issues)
}

/// Run parse + lower + resolve and allow undefined stdlib names.
fn parse_lower_and_resolve(path: &Path) -> (bool, Vec<String>) {
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => return (false, vec![format!("Failed to read file: {}", e)]),
    };

    let result = parse(&source);
    let mut issues = Vec::new();

    if !result.errors.is_empty() {
        for err in &result.errors {
            issues.push(format!("Parse error: {}", err.message));
        }
        return (false, issues);
    }

    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(FileId(0), &tree);

    if !lower_result.errors.is_empty() {
        for err in &lower_result.errors {
            issues.push(format!("Lowering error: {err:?}"));
        }
        return (false, issues);
    }

    let module = match lower_result.module {
        Some(m) => m,
        None => {
            issues.push("Lowering produced no module".to_string());
            return (false, issues);
        }
    };

    let resolve_result = resolve(&module);
    for err in resolve_result.errors {
        if !matches!(err.kind, ResolveErrorKind::Undefined { .. }) {
            issues.push(format!("Resolve error: {:?}", err.kind));
        }
    }

    (issues.is_empty(), issues)
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("tla-core must be nested under workspace root")
        .to_path_buf()
}

fn fixture_spec_paths() -> Vec<PathBuf> {
    let root = workspace_root();
    let rel_paths = [
        "tests/specs/LetBindingBug.tla",
        "tests/specs/LetBindingBug2.tla",
        "tests/tlc_comparison/repros/primed_arg_binding_804/PrimedArgBinding.tla",
    ];

    let mut specs = Vec::with_capacity(rel_paths.len());
    for rel_path in rel_paths {
        let spec = root.join(rel_path);
        assert!(
            spec.exists(),
            "fixture spec does not exist: {}",
            spec.display()
        );
        specs.push(spec);
    }
    specs
}

fn format_failures(failures: &[(String, Vec<String>)]) -> String {
    failures
        .iter()
        .map(|(path, issues)| format!("{}: {}", path, issues.join(" | ")))
        .collect::<Vec<_>>()
        .join("\n")
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_fixture_let_binding_bug() {
    let path = &fixture_spec_paths()[0];
    let (ok, issues) = parse_file(path);

    assert!(
        ok,
        "expected parser success for {} but saw issues: {:?}",
        path.display(),
        issues
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_fixture_let_binding_bug2() {
    let path = &fixture_spec_paths()[1];
    let (ok, issues) = parse_file(path);

    assert!(
        ok,
        "expected parser success for {} but saw issues: {:?}",
        path.display(),
        issues
    );
}

#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn test_bulk_parse_fixtures() {
    let tla_files = fixture_spec_paths();
    let total = tla_files.len();
    assert!(
        total > 0,
        "fixture_spec_paths must produce at least one spec"
    );

    let mut success = 0;
    let mut failures: Vec<(String, Vec<String>)> = Vec::new();

    for path in &tla_files {
        let (ok, issues) = parse_file(path);
        if ok {
            success += 1;
        } else {
            failures.push((path.display().to_string(), issues));
        }
    }

    assert_eq!(
        success,
        total,
        "parse failures:\n{}",
        format_failures(&failures)
    );
    assert!(
        failures.is_empty(),
        "parse failure set should be empty; total={} success={} failures={}",
        total,
        success,
        failures.len()
    );
}

#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn test_bulk_lower_fixtures() {
    let tla_files = fixture_spec_paths();
    let total = tla_files.len();
    assert!(
        total > 0,
        "fixture_spec_paths must produce at least one spec"
    );

    let mut success = 0;
    let mut failures: Vec<(String, Vec<String>)> = Vec::new();

    for path in &tla_files {
        let (ok, issues) = parse_and_lower(path);
        if ok {
            success += 1;
        } else {
            failures.push((path.display().to_string(), issues));
        }
    }

    assert_eq!(
        success,
        total,
        "lowering failures:\n{}",
        format_failures(&failures)
    );
    assert!(
        failures.is_empty(),
        "lowering failure set should be empty; total={} success={} failures={}",
        total,
        success,
        failures.len()
    );
}

#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn test_bulk_resolve_fixtures() {
    let tla_files = fixture_spec_paths();
    let total = tla_files.len();
    assert!(
        total > 0,
        "fixture_spec_paths must produce at least one spec"
    );

    let mut success = 0;
    let mut failures: Vec<(String, Vec<String>)> = Vec::new();

    for path in &tla_files {
        let (ok, issues) = parse_lower_and_resolve(path);
        if ok {
            success += 1;
        } else {
            failures.push((path.display().to_string(), issues));
        }
    }

    assert_eq!(
        success,
        total,
        "resolve failures:\n{}",
        format_failures(&failures)
    );
    assert!(
        failures.is_empty(),
        "resolve failure set should be empty; total={} success={} failures={}",
        total,
        success,
        failures.len()
    );
}
