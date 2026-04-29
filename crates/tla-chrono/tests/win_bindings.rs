use std::{env, fs, process};
use windows_bindgen::bindgen;

#[test]
fn gen_bindings() {
    let existing = fs::read_to_string(BINDINGS).unwrap();
    assert!(existing.contains("// Copyright 2026 Dropbox"));
    assert!(existing.contains("// Author: Andrew Yates"));
    assert!(existing.contains("// Licensed under the Apache License, Version 2.0"));

    let generated = env::temp_dir().join(format!("chrono-win-bindings-{}.rs", process::id()));
    let generated = generated.to_str().unwrap();
    bindgen([
        "--out",
        generated,
        "--flat",
        "--no-comment",
        "--no-deps",
        "--sys",
        "--filter",
        "GetTimeZoneInformationForYear",
        "SystemTimeToFileTime",
        "SystemTimeToTzSpecificLocalTime",
        "TzSpecificLocalTimeToSystemTime",
    ])
    .unwrap();

    let new = fs::read_to_string(generated).unwrap();
    let _ = fs::remove_file(generated);

    let existing = normalized_generated_body(&existing);
    let new = normalized_generated_body(&new);

    similar_asserts::assert_eq!(existing, new);
    if !new.lines().eq(existing.lines()) {
        panic!("generated file `{BINDINGS}` is changed.");
    }
}

fn normalized_generated_body(source: &str) -> String {
    let mut normalized = Vec::new();
    let mut removed_header = false;
    let normalized_source = source.replace("\r\n", "\n");
    for line in normalized_source.lines() {
        if matches!(
            line,
            "// Copyright 2026 Dropbox"
                | "// Copyright 2026 Dropbox, Inc."
                | "// Author: Andrew Yates <ayates@dropbox.com>"
                | "// Licensed under the Apache License, Version 2.0"
        ) {
            removed_header = true;
            continue;
        }
        if removed_header && line.trim().is_empty() {
            removed_header = false;
            continue;
        }
        removed_header = false;
        normalized.push(line);
    }
    normalized.join("\n")
}

const BINDINGS: &str = "src/offset/local/win_bindings.rs";
