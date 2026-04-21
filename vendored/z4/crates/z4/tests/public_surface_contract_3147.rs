// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guardrail test: docs/CONSUMER_MIGRATION.md must stay aligned with the
//! actual root-crate public surface defined in crates/z4/src/lib.rs.
//!
//! Part of #3147 — API contract drift prevention.

const MIGRATION_DOC: &str = include_str!("../../../docs/CONSUMER_MIGRATION.md");

/// Extract the "Available Root Crate Surfaces" section from the migration doc.
fn extract_root_surface_section(doc: &str) -> &str {
    let heading = "## Available Root Crate Surfaces";
    let start = doc
        .find(heading)
        .expect("CONSUMER_MIGRATION.md must contain '## Available Root Crate Surfaces'");
    let section = &doc[start..];
    // End at the next H2 heading or end-of-file.
    if let Some(next) = section[heading.len()..].find("\n## ") {
        &section[..heading.len() + next]
    } else {
        section
    }
}

#[test]
fn test_consumer_migration_root_surface_table_matches_facade() {
    let section = extract_root_surface_section(MIGRATION_DOC);

    // Positive: all implemented surfaces must be documented.
    assert!(
        section.contains("z4::api"),
        "migration doc must document z4::api"
    );
    assert!(
        section.contains("z4::chc"),
        "migration doc must document z4::chc"
    );
    assert!(
        section.contains("z4::executor"),
        "migration doc must document z4::executor"
    );
    assert!(
        section.contains("z4::prelude"),
        "migration doc must document z4::prelude"
    );
    assert!(
        section.contains("z4::Solver"),
        "migration doc must document root flat import z4::Solver"
    );

    // Negative: removed/non-existent surfaces must not be advertised.
    assert!(
        !section.contains("z4::core"),
        "migration doc must NOT advertise z4::core (not a real module)"
    );
    assert!(
        !section.contains("z4::theories"),
        "migration doc must NOT advertise z4::theories (not a real module)"
    );
}
