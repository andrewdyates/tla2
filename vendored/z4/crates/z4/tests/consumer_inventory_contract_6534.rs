// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
//! Contract test: docs/integrations/consumer_inventory.tsv stays consistent
//! with VISION.md, CONSUMER_MIGRATION.md, and CROSS_REPO_PATTERNS.md.
//!
//! This test fails if the canonical inventory and docs drift apart.
//! See #6534 and designs/2026-03-13-issue-6534-canonical-consumer-inventory.md.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    Path::new(&manifest)
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

#[derive(Debug)]
struct InventoryRow {
    name: String,
    include_in_vision: bool,
    include_in_migration: bool,
    include_in_patterns: bool,
    smoke_script: String,
    tracking_state: String,
}

fn parse_inventory() -> Vec<InventoryRow> {
    let root = repo_root();
    let tsv_path = root.join("docs/integrations/consumer_inventory.tsv");
    let content = std::fs::read_to_string(&tsv_path)
        .unwrap_or_else(|e| panic!("cannot read {}: {}", tsv_path.display(), e));

    let mut rows = Vec::new();
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        // Skip header
        if line.starts_with("name\t") {
            continue;
        }
        let cols: Vec<&str> = line.split('\t').collect();
        assert!(
            cols.len() >= 9,
            "inventory row has {} columns, expected 9: {}",
            cols.len(),
            line
        );
        rows.push(InventoryRow {
            name: cols[0].to_string(),
            include_in_vision: cols[2] == "1",
            include_in_migration: cols[3] == "1",
            include_in_patterns: cols[4] == "1",
            smoke_script: cols[6].to_string(),
            tracking_state: cols[7].to_string(),
        });
    }
    assert!(!rows.is_empty(), "inventory is empty");
    rows
}

#[test]
fn test_inventory_file_exists_and_is_parseable() {
    let rows = parse_inventory();
    assert!(
        rows.len() >= 5,
        "expected at least 5 consumer rows, got {}",
        rows.len()
    );

    let names: Vec<&str> = rows.iter().map(|r| r.name.as_str()).collect();
    for required in &["zani", "sunder", "certus", "tla2", "lean5"] {
        assert!(
            names.contains(required),
            "missing required consumer: {required}"
        );
    }
}

#[test]
fn test_vision_md_contains_inventory_consumers() {
    let root = repo_root();
    let vision = std::fs::read_to_string(root.join("VISION.md")).expect("read VISION.md");
    let rows = parse_inventory();

    for row in &rows {
        if row.include_in_vision {
            assert!(
                vision.contains(&row.name),
                "VISION.md should contain consumer '{}' (include_in_vision=1 in inventory)",
                row.name
            );
        }
    }
}

#[test]
fn test_migration_md_contains_inventory_consumers() {
    let root = repo_root();
    let migration = std::fs::read_to_string(root.join("docs/CONSUMER_MIGRATION.md"))
        .expect("read CONSUMER_MIGRATION.md");
    let rows = parse_inventory();

    for row in &rows {
        if row.include_in_migration {
            assert!(
                migration.contains(&row.name),
                "CONSUMER_MIGRATION.md should contain consumer '{}' (include_in_migration=1 in inventory)",
                row.name
            );
        }
    }
}

#[test]
fn test_patterns_md_contains_inventory_consumers() {
    let root = repo_root();
    let patterns = std::fs::read_to_string(root.join("docs/integrations/CROSS_REPO_PATTERNS.md"))
        .expect("read CROSS_REPO_PATTERNS.md");
    let rows = parse_inventory();

    for row in &rows {
        if row.include_in_patterns {
            assert!(
                patterns.contains(&row.name),
                "CROSS_REPO_PATTERNS.md should contain consumer '{}' (include_in_patterns=1 in inventory)",
                row.name
            );
        }
    }
}

#[test]
fn test_smoke_scripts_exist() {
    let root = repo_root();
    let rows = parse_inventory();

    for row in &rows {
        if row.smoke_script != "-" && !row.smoke_script.is_empty() {
            let script_path = root.join("scripts").join(&row.smoke_script);
            assert!(
                script_path.exists(),
                "smoke script '{}' for consumer '{}' does not exist at {}",
                row.smoke_script,
                row.name,
                script_path.display()
            );
        }
    }
}

#[test]
fn test_no_duplicate_names() {
    let rows = parse_inventory();
    let mut seen = HashSet::new();
    for row in &rows {
        assert!(
            seen.insert(&row.name),
            "duplicate consumer name in inventory: {}",
            row.name
        );
    }
}

#[test]
fn test_tracking_state_is_valid() {
    let valid_states = [
        "active",
        "smoke_only",
        "canary_only",
        "tracked_no_local_smoke",
    ];
    let rows = parse_inventory();
    for row in &rows {
        assert!(
            valid_states.contains(&row.tracking_state.as_str()),
            "consumer '{}' has invalid tracking_state '{}', expected one of {:?}",
            row.name,
            row.tracking_state,
            valid_states
        );
    }
}
