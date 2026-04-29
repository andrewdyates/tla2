// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 enabled` — find ENABLED expressions.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EnabledOutputFormat {
    Human,
    Json,
}

pub(crate) fn cmd_enabled(file: &Path, format: EnabledOutputFormat) -> Result<()> {
    let start = Instant::now();
    let source = read_source(file)?;
    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        let fp = file.display().to_string();
        for err in &lower_result.errors {
            tla_core::lower_error_diagnostic(&fp, &err.message, err.span).eprint(&fp, &source);
        }
        bail!(
            "lowering failed with {} error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result.module.context("lowering produced no module")?;

    let mut entries: Vec<(String, String)> = Vec::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            find_enabled(&def.body.node, &def.name.node, &mut entries);
        }
    }
    let elapsed = start.elapsed().as_secs_f64();

    match format {
        EnabledOutputFormat::Human => {
            println!("enabled: {}", file.display());
            println!("  ENABLED expressions: {}", entries.len());
            println!();
            for (op, expr) in &entries {
                println!("  {op}: ENABLED {expr}");
            }
            println!("\n  elapsed: {elapsed:.2}s");
        }
        EnabledOutputFormat::Json => {
            let json: Vec<serde_json::Value> = entries
                .iter()
                .map(|(op, expr)| serde_json::json!({"operator": op, "expression": expr}))
                .collect();
            let output = serde_json::json!({"version":"0.1.0","file":file.display().to_string(),"enabled_expressions":json,"elapsed_seconds":elapsed});
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }
    Ok(())
}

fn find_enabled(expr: &Expr, op_name: &str, entries: &mut Vec<(String, String)>) {
    match expr {
        Expr::Enabled(inner) => {
            let text = pretty_expr(&inner.node);
            let truncated = if text.len() > 80 {
                format!("{}...", &text[..77])
            } else {
                text
            };
            entries.push((op_name.to_string(), truncated));
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b) => {
            find_enabled(&a.node, op_name, entries);
            find_enabled(&b.node, op_name, entries);
        }
        Expr::If(c, t, e) => {
            find_enabled(&c.node, op_name, entries);
            find_enabled(&t.node, op_name, entries);
            find_enabled(&e.node, op_name, entries);
        }
        Expr::Forall(_, body) | Expr::Exists(_, body) => find_enabled(&body.node, op_name, entries),
        _ => {}
    }
}
