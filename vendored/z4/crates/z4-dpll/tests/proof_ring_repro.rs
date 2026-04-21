// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::fs;
use std::path::Path;
use z4_dpll::Executor;
use z4_frontend::parse;

fn workspace_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
}

fn solve_with_proof(path: &str) -> bool {
    let path = workspace_root().join(path);
    let content = fs::read_to_string(&path).expect("read benchmark");
    let content = content
        .lines()
        .filter(|line| line.trim() != "(exit)")
        .collect::<Vec<_>>()
        .join("\n");
    let script = format!("(set-option :produce-proofs true)\n{content}\n(get-proof)\n");
    let commands = parse(&script).expect("parse benchmark");
    let mut exec = Executor::new();
    eprintln!("SOLVING {}", path.display());
    let outputs = exec.execute_all(&commands).expect("execute benchmark");
    if outputs.first().map(String::as_str) != Some("unsat") {
        eprintln!(
            "SKIP {} result={:?}",
            path.display(),
            outputs.first().map(String::as_str)
        );
        return false;
    }
    assert!(
        outputs
            .last()
            .is_some_and(|proof| proof.contains("(assume ") || proof.contains("(step ")),
        "expected proof output for {}: {outputs:?}",
        path.display()
    );
    true
}

fn collect_unsat_benchmarks() -> Vec<String> {
    let smt_dir = workspace_root().join("benchmarks/smt");
    let mut files = Vec::new();
    for entry in fs::read_dir(&smt_dir).expect("read benchmarks/smt") {
        let subdir = entry.expect("read dir entry").path();
        if !subdir.is_dir() {
            continue;
        }
        for file_entry in fs::read_dir(&subdir).expect("read logic subdir") {
            let path = file_entry.expect("read file entry").path();
            if path.extension().is_some_and(|ext| ext == "smt2") {
                let name = path
                    .file_name()
                    .and_then(|n| n.to_str())
                    .unwrap_or_default();
                if name.contains("unsat") {
                    files.push(
                        path.strip_prefix(workspace_root())
                            .expect("path under workspace")
                            .display()
                            .to_string(),
                    );
                }
            }
        }
    }
    files.sort();
    files
}

#[test]
fn test_ring_benchmark_proof_generation() {
    for path in [
        "benchmarks/smt/QF_LIA/ring_2exp12_3vars_deep_unsat.smt2",
        "benchmarks/smt/QF_LIA/ring_2exp16_5vars_cascade_unsat.smt2",
        "benchmarks/smt/QF_LIA/ring_2exp16_5vars_cascade_v2_unsat.smt2",
        "benchmarks/smt/QF_LIA/ring_2exp4_3vars_0ite_unsat.smt2",
        "benchmarks/smt/QF_LIA/ring_2exp8_3vars_crt_unsat.smt2",
        "benchmarks/smt/QF_LIA/ring_2exp8_4vars_carry_unsat.smt2",
        "benchmarks/smt/QF_LIA/ring_2exp8_5vars_modular_unsat.smt2",
    ] {
        assert!(
            solve_with_proof(path),
            "ring benchmark unexpectedly did not solve as UNSAT: {path}"
        );
    }
}

#[test]
fn test_unsat_benchmark_proof_generation_with_labels() {
    for path in collect_unsat_benchmarks() {
        let _ = solve_with_proof(&path);
    }
}

#[test]
fn test_unsat_implied_equality_proof_generation() {
    assert!(
        solve_with_proof("benchmarks/smt/QF_UFLIA/unsat_implied_equality.smt2"),
        "expected UNSAT proof for unsat_implied_equality"
    );
}
