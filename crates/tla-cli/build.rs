// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Build script: embeds `TLA2_GIT_COMMIT` at compile time.

fn main() {
    // Embed git commit hash so `tla2 diagnose --output json` can report it.
    let commit = std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map_or_else(
            || "unknown".to_string(),
            |o| String::from_utf8_lossy(&o.stdout).trim().to_string(),
        );

    println!("cargo:rustc-env=TLA2_GIT_COMMIT={commit}");

    // Re-run if HEAD changes (new commit).
    println!("cargo:rerun-if-changed=../../.git/HEAD");
    println!("cargo:rerun-if-changed=../../.git/refs/heads/");
}
