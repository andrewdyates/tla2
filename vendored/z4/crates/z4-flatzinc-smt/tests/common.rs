// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[allow(dead_code)]
pub(crate) fn z4_path() -> Option<String> {
    if let Ok(path) = std::env::var("Z4_PATH") {
        if std::path::Path::new(&path).exists() {
            return Some(path);
        }
    }

    let home = std::env::var("HOME").expect("HOME env var required");
    let default = format!("{home}/z4/target/release/z4");
    if std::path::Path::new(&default).exists() {
        Some(default)
    } else {
        None
    }
}

#[allow(dead_code)]
fn allow_missing_z4_binary() -> bool {
    matches!(
        std::env::var("Z4_SUBPROCESS_TESTS_ALLOW_MISSING_BINARY")
            .ok()
            .as_deref(),
        Some("1" | "true" | "TRUE" | "yes" | "YES")
    )
}

#[allow(dead_code)]
pub(crate) fn require_z4_path_for_subprocess_tests() -> Option<String> {
    match z4_path() {
        Some(path) => Some(path),
        None if allow_missing_z4_binary() => {
            eprintln!(
                "z4 subprocess binary missing; explicit skip via \
Z4_SUBPROCESS_TESTS_ALLOW_MISSING_BINARY=1"
            );
            None
        }
        None => panic!(
            "z4 subprocess tests require a solver binary. Set Z4_PATH or build \
target/release/z4. To skip intentionally, set \
Z4_SUBPROCESS_TESTS_ALLOW_MISSING_BINARY=1."
        ),
    }
}
