// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use num_bigint::BigInt;
use z4_core::{FarkasAnnotation, LiaAnnotation, Proof, Sort, TermStore, TheoryLemmaKind};
use z4_proof::{check_proof_strict, export_alethe, export_alethe_with_problem_scope};

static TEMP_FILE_SEQ: AtomicU64 = AtomicU64::new(0);

const QF_BOOL_AND_UNSAT: &str = r#"
(set-logic QF_BOOL)
(declare-const a Bool)
(declare-const b Bool)
(assert (and a b))
(assert (not b))
(check-sat)
"#;

const QF_LRA_UNSAT: &str = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (<= x 5.0))
(assert (<= 10.0 x))
(check-sat)
"#;

const QF_LIA_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (<= x 5))
(assert (<= 10 x))
(check-sat)
"#;

#[test]
fn exports_clausification_rule_args_in_alethe_syntax() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = terms.mk_and(vec![a, b]);
    let or_ab = terms.mk_or(vec![a, b]);
    let not_and_ab = terms.mk_not_raw(and_ab);
    let not_b = terms.mk_not(b);

    let mut proof = Proof::new();
    proof.add_rule_step(
        z4_core::AletheRule::AndPos(1),
        vec![not_and_ab, b],
        vec![],
        vec![and_ab],
    );
    proof.add_rule_step(
        z4_core::AletheRule::OrNeg,
        vec![or_ab, not_b],
        vec![],
        vec![or_ab],
    );

    let output = export_alethe(&proof, &terms);
    assert!(
        output.contains("(step t0 (cl (not (and a b)) b) :rule and_pos :args (1))"),
        "{output}"
    );
    assert!(
        output.contains("(step t1 (cl (or a b) (not b)) :rule or_neg :args (1))"),
        "{output}"
    );
    assert!(
        !output.contains(":args ((and a b))"),
        "internal source-term arg must not leak into Alethe output:\n{output}"
    );
    assert!(
        !output.contains(":args ((or a b))"),
        "internal source-term arg must not leak into Alethe output:\n{output}"
    );
}

#[test]
fn exports_boolean_and_certificate_that_carcara_accepts() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = terms.mk_and(vec![a, b]);
    let not_and_ab = terms.mk_not_raw(and_ab);
    let not_b = terms.mk_not(b);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(and_ab, None);
    let t1 = proof.add_rule_step(
        z4_core::AletheRule::AndPos(1),
        vec![not_and_ab, b],
        vec![],
        vec![and_ab],
    );
    let t2 = proof.add_resolution(vec![b], and_ab, h0, t1);
    let h3 = proof.add_assume(not_b, None);
    proof.add_resolution(vec![], b, t2, h3);

    check_proof_strict(&proof, &terms).expect("Boolean proof should validate strictly");

    let alethe = export_alethe_with_problem_scope(&proof, &terms, &[and_ab, not_b]);
    assert!(
        alethe.contains(":rule and_pos :args (1)"),
        "expected translated and_pos args:\n{alethe}"
    );
    assert_carcara_accepts("bool_and", QF_BOOL_AND_UNSAT, &alethe);
}

#[test]
fn exports_lra_certificate_that_carcara_accepts() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(num_rational::BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(num_rational::BigRational::from(BigInt::from(10)));
    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);
    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x_le_5, None);
    let h1 = proof.add_assume(x_ge_10, None);
    let t2 = proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_x_le_5, not_x_ge_10],
        FarkasAnnotation::from_ints(&[1, 1]),
    );
    let t3 = proof.add_resolution(vec![not_x_ge_10], x_le_5, h0, t2);
    proof.add_resolution(vec![], x_ge_10, h1, t3);

    check_proof_strict(&proof, &terms).expect("LRA proof should validate strictly");

    let alethe = export_alethe_with_problem_scope(&proof, &terms, &[x_le_5, x_ge_10]);
    assert!(
        alethe.contains(":rule la_generic :args (1 1)"),
        "expected Farkas args in Alethe output:\n{alethe}"
    );
    assert_carcara_accepts("lra_bounds_gap", QF_LRA_UNSAT, &alethe);
}

#[test]
fn exports_lia_certificate_that_is_strictly_valid_and_carcara_parseable() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));
    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);
    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x_le_5, None);
    let h1 = proof.add_assume(x_ge_10, None);
    let t2 = proof.add_theory_lemma_with_lia(
        "LIA",
        vec![not_x_le_5, not_x_ge_10],
        Some(FarkasAnnotation::from_ints(&[1, 1])),
        TheoryLemmaKind::LiaGeneric,
        LiaAnnotation::BoundsGap,
    );
    let t3 = proof.add_resolution(vec![not_x_ge_10], x_le_5, h0, t2);
    proof.add_resolution(vec![], x_ge_10, h1, t3);

    check_proof_strict(&proof, &terms).expect("LIA proof should validate strictly");

    let alethe = export_alethe_with_problem_scope(&proof, &terms, &[x_le_5, x_ge_10]);
    assert!(
        alethe.contains(":rule lia_generic :args (1 1)"),
        "expected lia_generic export with Farkas args:\n{alethe}"
    );
    assert_carcara_accepts("lia_bounds_gap", QF_LIA_UNSAT, &alethe);
}

fn assert_carcara_accepts(label: &str, problem: &str, proof: &str) {
    let Some(carcara) = find_carcara() else {
        eprintln!("carcara not found, skipping external Alethe validation for {label}");
        return;
    };

    let (problem_path, proof_path) = write_problem_and_proof(label, problem, proof);
    let output = Command::new(carcara)
        .arg("check")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara check");

    let _ = std::fs::remove_file(&problem_path);
    let _ = std::fs::remove_file(&proof_path);

    assert!(
        output.status.success(),
        "carcara rejected generated Alethe proof ({label})\nstderr: {}\nproof:\n{}",
        String::from_utf8_lossy(&output.stderr),
        proof
    );
}

fn find_carcara() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("CARCARA_PATH") {
        let path = PathBuf::from(path);
        if path.is_file() {
            return Some(path);
        }
    }

    let candidates = [
        PathBuf::from("./.cargo/bin/carcara"),
        PathBuf::from("/usr/local/bin/carcara"),
        PathBuf::from("/opt/homebrew/bin/carcara"),
    ];
    for candidate in candidates {
        if candidate.is_file() {
            return Some(candidate);
        }
    }

    let path_var = std::env::var_os("PATH")?;
    for dir in std::env::split_paths(&path_var) {
        let candidate = dir.join("carcara");
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn write_problem_and_proof(label: &str, problem: &str, proof: &str) -> (PathBuf, PathBuf) {
    let run_id = TEMP_FILE_SEQ.fetch_add(1, Ordering::Relaxed);
    let suffix = format!("{}_{}_{}", label, std::process::id(), run_id);
    let problem_path = std::env::temp_dir().join(format!("z4_proof_problem_{suffix}.smt2"));
    let proof_path = std::env::temp_dir().join(format!("z4_proof_proof_{suffix}.alethe"));

    std::fs::write(&problem_path, problem).unwrap_or_else(|e| {
        panic!(
            "failed to write problem file {}: {e}",
            display_path(&problem_path)
        )
    });
    std::fs::write(&proof_path, proof).unwrap_or_else(|e| {
        panic!(
            "failed to write proof file {}: {e}",
            display_path(&proof_path)
        )
    });

    (problem_path, proof_path)
}

fn display_path(path: &Path) -> String {
    path.display().to_string()
}
