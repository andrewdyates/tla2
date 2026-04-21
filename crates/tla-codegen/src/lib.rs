// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
#![forbid(unsafe_code)]
// Code generation modules build Rust source text via push_str(&format!(...)).
#![allow(clippy::format_push_string)]

//! TLA+ to Rust Code Generator
//!
//! This crate generates Rust code from TLA+ specifications. The generated code
//! implements the `StateMachine` trait from `tla-runtime`, enabling:
//!
//! - Runtime execution of TLA+ state machines
//! - Integration with property-based testing (proptest)
//! - Integration with verification tools (Kani)
//!
//! # Architecture
//!
//! 1. **Type Inference**: Infer Rust types from TLA+ expressions
//! 2. **Code Generation**: Emit Rust code implementing StateMachine trait
//!
//! # Limitations
//!
//! Not all TLA+ constructs can be translated to Rust:
//! - Infinite sets (e.g., Nat, Int) require bounded approximations
//! - Higher-order operators require special handling
//! - Temporal operators are not supported (use model checker instead)

#[allow(dead_code)]
mod codegen_source_map;
mod emit;
pub mod error;
#[cfg(any(kani, test))]
mod kani_demo;
pub mod tir_emit;
mod types;
pub mod z4_codegen;

use std::collections::BTreeMap;
use tla_core::ast::Module;

use codegen_source_map::CodegenEntryKind;
pub use codegen_source_map::CodegenSourceMap;

pub use emit::{generate_rust, generate_rust_with_context, CodeGenOptions};
pub use error::CodegenError;
pub use tir_emit::{
    expr_contains_prime_pub, generate_rust_from_tir, generate_rust_from_tir_with_modules,
    TirCodeGenOptions,
};
pub use types::struct_registry::StructRegistry;
pub use types::{TlaType, TypeContext, TypeInferError};
pub use z4_codegen::{generate_rust_module, generate_rust_module_with_options, Z4CodegenOptions};

/// Generate Rust code from a TLA+ module and produce a companion source map.
///
/// This wraps [`generate_rust_with_context`] and then post-processes the
/// generated Rust text to build a [`CodegenSourceMap`] that records which
/// TLA+ operators correspond to which line ranges in the output.
pub fn generate_rust_with_source_map(
    module: &Module,
    context: &CodeGenContext<'_>,
    options: &CodeGenOptions,
    generated_file: &str,
    tla_source: &str,
) -> Result<(String, CodegenSourceMap), CodegenError> {
    let rust_code = generate_rust_with_context(module, context, options)?;
    let source_map = build_source_map_from_generated(&rust_code, generated_file, tla_source);
    Ok((rust_code, source_map))
}

/// Build a source map by scanning the generated Rust code for known patterns.
fn build_source_map_from_generated(
    rust_code: &str,
    generated_file: &str,
    tla_source: &str,
) -> CodegenSourceMap {
    let mut source_map = CodegenSourceMap::new(generated_file, tla_source);
    let lines: Vec<&str> = rust_code.lines().collect();

    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim();
        let line_num = (i + 1) as u32;

        if line.starts_with("pub struct ") && line.ends_with("State {") {
            let struct_name = line
                .strip_prefix("pub struct ")
                .and_then(|s| s.strip_suffix(" {"))
                .unwrap_or("State");
            let end = find_closing_brace(&lines, i);
            source_map.add_entry(struct_name, CodegenEntryKind::StateStruct, line_num, (end + 1) as u32);
            i = end + 1;
            continue;
        }

        if line.starts_with("fn init(") {
            let end = find_closing_brace(&lines, i);
            source_map.add_entry("Init", CodegenEntryKind::Init, line_num, (end + 1) as u32);
            i = end + 1;
            continue;
        }

        if line.starts_with("fn next(") {
            let end = find_closing_brace(&lines, i);
            source_map.add_entry("Next", CodegenEntryKind::Next, line_num, (end + 1) as u32);
            i = end + 1;
            continue;
        }

        if line.starts_with("fn check_invariant(") || line.starts_with("fn inv_") {
            let fn_name = line
                .strip_prefix("fn ")
                .and_then(|s| s.split('(').next())
                .unwrap_or("invariant");
            let end = find_closing_brace(&lines, i);
            source_map.add_entry(fn_name, CodegenEntryKind::Invariant, line_num, (end + 1) as u32);
            i = end + 1;
            continue;
        }

        i += 1;
    }

    source_map
}

fn find_closing_brace(lines: &[&str], start: usize) -> usize {
    let mut depth = 0i32;
    for (j, line) in lines.iter().enumerate().skip(start) {
        for ch in line.chars() {
            if ch == '{' {
                depth += 1;
            } else if ch == '}' {
                depth -= 1;
                if depth == 0 {
                    return j;
                }
            }
        }
    }
    start
}

/// Additional modules available during code generation.
///
/// Parsed by the CLI and passed into `tla-codegen`; `tla-codegen` itself does not do file I/O.
#[derive(Debug, Clone, Default)]
pub struct CodeGenContext<'a> {
    /// Non-main modules reachable from the root spec via `EXTENDS` / `INSTANCE`.
    pub modules: Vec<&'a Module>,
}

/// Mapping config for generating `impl checker::To<Spec>State` blocks.
///
/// Parsed by the CLI and passed into `tla-codegen`; `tla-codegen` itself does not do file I/O.
#[derive(Debug, Clone, Default)]
pub struct CheckerMapConfig {
    /// Optional module name the config is intended for (e.g. `"Counter"`).
    ///
    /// If present, codegen rejects mismatches.
    pub spec_module: Option<String>,
    /// One or more adapter impl blocks to generate.
    pub impls: Vec<CheckerMapImpl>,
}

#[derive(Debug, Clone, Default)]
pub struct CheckerMapImpl {
    /// Rust type path to implement `checker::To<Spec>State` for.
    pub rust_type: String,
    /// Mapping from generated state field name (snake_case) to a single Rust expression.
    pub fields: BTreeMap<String, String>,
}
