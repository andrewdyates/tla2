// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared helper for tla-codegen integration tests.

use tla_codegen::{generate_rust, CodeGenOptions};
use tla_core::{compute_is_recursive, lower, parse, FileId};

pub fn parse_and_generate(source: &str, options: &CodeGenOptions) -> Result<String, String> {
    let parsed = parse(source);
    if !parsed.errors.is_empty() {
        let msgs: Vec<_> = parsed.errors.iter().map(|e| e.message.clone()).collect();
        return Err(format!("Parse errors: {}", msgs.join(", ")));
    }

    let tree = tla_core::SyntaxNode::new_root(parsed.green_node);
    let result = lower(FileId(0), &tree);

    if !result.errors.is_empty() {
        let msgs: Vec<_> = result.errors.iter().map(|e| e.message.clone()).collect();
        return Err(format!("Lower errors: {}", msgs.join(", ")));
    }

    let mut module = result
        .module
        .ok_or_else(|| "No module produced".to_string())?;
    compute_is_recursive(&mut module);

    generate_rust(&module, options).map_err(|e| e.to_string())
}
