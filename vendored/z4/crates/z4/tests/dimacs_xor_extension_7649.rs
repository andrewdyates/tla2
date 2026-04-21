// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp_cnf(contents: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "z4_dimacs_xor_extension_{}_{}.cnf",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("failed to write temp cnf");
    (path.clone(), CleanupGuard(path))
}

#[test]
#[timeout(60_000)]
fn test_dimacs_xor_detection_routes_nonproof_solver_through_extension() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    // Pure-XOR formula:
    //   x1 XOR x2 = 1  => (-x1 OR -x2) AND (x1 OR x2)
    // Both clauses should be consumed by z4-xor preprocessing, leaving a
    // pure-XOR SAT instance on the extension path.
    let cnf = "p cnf 2 2\n-1 -2 0\n1 2 0\n";
    let (input_path, _cleanup) = write_temp_cnf(cnf);

    let output = Command::new(z4_path)
        .arg(&input_path)
        .output()
        .expect("failed to spawn z4");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(
        output.status.code(),
        Some(10),
        "expected DIMACS SAT exit code 10, stderr: {stderr}"
    );
    assert!(
        stdout.contains("s SATISFIABLE"),
        "expected DIMACS SAT output, got {stdout}"
    );
    assert!(
        stderr.contains("c XOR: detected 1 constraints, 2 clauses consumed"),
        "expected XOR preprocessing banner, got {stderr}"
    );
}
