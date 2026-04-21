// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::process::Command;

#[test]
#[timeout(30_000)]
fn test_arrays_row2_propagation_regression() {
    let z4_path = env!("CARGO_BIN_EXE_z4");

    let test_input = r#"(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (not (= i j)))  ; i != j

(declare-const v Int)
(declare-const A_post (Array Int Int))
(assert (= A_post (store A i v)))

(declare-const before Int)
(declare-const after Int)
(assert (= before (select A j)))
(assert (= after (select A_post j)))

; ROW2 should derive: before = after
(assert (not (= before after)))
(check-sat)
"#;

    let temp_path = {
        use std::time::{SystemTime, UNIX_EPOCH};
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time after unix epoch")
            .as_nanos();
        let pid = std::process::id();
        std::env::temp_dir().join(format!("z4_arrays_row2_regression_{pid}_{nanos}.smt2"))
    };

    std::fs::write(&temp_path, test_input).unwrap();
    // Clean up temp file when done (uses Drop guard)
    struct CleanupGuard(std::path::PathBuf);
    impl Drop for CleanupGuard {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    let _cleanup = CleanupGuard(temp_path.clone());

    let output = Command::new(z4_path)
        .arg(&temp_path)
        .output()
        .expect("Failed to run z4");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    eprintln!("Z4 stdout: {stdout:?}");
    eprintln!("Z4 stderr: {stderr:?}");
    eprintln!("Z4 exit: {:?}", output.status);

    assert!(
        output.status.success(),
        "Z4 exited with {:?}",
        output.status
    );
    let first_line = stdout.lines().next().unwrap_or("");
    assert_eq!(first_line, "unsat", "Expected 'unsat', got: {stdout}");
}
