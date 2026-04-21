// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Build script: embeds git commit hash and build timestamp into the binary.
//!
//! These are available at compile time via `env!("Z4_GIT_HASH")` etc.
//! Zero runtime overhead — the values are baked into the binary as string constants.

use std::process::Command;

fn main() {
    // Git short hash (7 chars)
    let git_hash = Command::new("git")
        .args(["rev-parse", "--short=10", "HEAD"])
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());

    // Dirty flag
    let git_dirty = Command::new("git")
        .args(["status", "--porcelain"])
        .output()
        .ok()
        .map(|o| !o.stdout.is_empty())
        .unwrap_or(false);

    let hash_suffix = if git_dirty { "+dirty" } else { "" };

    // Build timestamp in Pacific time with timezone
    let build_date = Command::new("date")
        .args(["+%Y-%m-%d %H:%M %Z"])
        .env("TZ", "America/Los_Angeles")
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());

    // Commit count (for a monotonically increasing build number)
    let commit_count = Command::new("git")
        .args(["rev-list", "--count", "HEAD"])
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "0".to_string());

    // Build profile: "release" or "debug"
    let profile = std::env::var("PROFILE").unwrap_or_else(|_| "unknown".to_string());

    println!("cargo:rustc-env=Z4_GIT_HASH={git_hash}{hash_suffix}");
    println!("cargo:rustc-env=Z4_BUILD_DATE={build_date}");
    println!("cargo:rustc-env=Z4_COMMIT_COUNT={commit_count}");
    println!("cargo:rustc-env=Z4_BUILD_PROFILE={profile}");

    // Only re-run if git HEAD changes (not on every file change)
    println!("cargo:rerun-if-changed=../../.git/HEAD");
    println!("cargo:rerun-if-changed=../../.git/index");
}
