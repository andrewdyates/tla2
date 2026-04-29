// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 case-count` — count CASE expressions.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CasecountOutputFormat {
    Human,
    Json,
}

pub(crate) fn cmd_casecount(file: &Path, format: CasecountOutputFormat) -> Result<()> {
    let start = Instant::now();
    let source = read_source(file)?;
    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let d = tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            d.eprint(&file_path, &source);
        }
        bail!(
            "lowering failed with {} error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result.module.context("lowering produced no module")?;

    let mut ops: Vec<(String, usize)> = Vec::new();
    let mut total = 0usize;
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            let count = count_case(&def.body.node);
            total += count;
            if count > 0 {
                ops.push((def.name.node.clone(), count));
            }
        }
    }
    ops.sort_by(|a, b| b.1.cmp(&a.1));
    let elapsed = start.elapsed().as_secs_f64();

    match format {
        CasecountOutputFormat::Human => {
            println!("case-count: {}", file.display());
            println!("  total CASE: {total}");
            println!("  operators with CASE: {}", ops.len());
            for (n, c) in &ops {
                println!("  {n}: {c}");
            }
            println!("\n  elapsed: {elapsed:.2}s");
        }
        CasecountOutputFormat::Json => {
            let ops_json: Vec<serde_json::Value> = ops
                .iter()
                .map(|(n, c)| serde_json::json!({"name": n, "count": c}))
                .collect();
            let output = serde_json::json!({"version":"0.1.0","file":file.display().to_string(),"total":total,"operators":ops_json,"elapsed_seconds":elapsed});
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }
    Ok(())
}

fn count_case(expr: &Expr) -> usize {
    match expr {
        Expr::Case(arms, other) => {
            let arm_count: usize = arms
                .iter()
                .map(|arm| count_case(&arm.guard.node) + count_case(&arm.body.node))
                .sum();
            let other_count = other.as_ref().map(|o| count_case(&o.node)).unwrap_or(0);
            1 + arm_count + other_count
        }
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Lt(a, b)
        | Expr::Gt(a, b)
        | Expr::Leq(a, b)
        | Expr::Geq(a, b)
        | Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Div(a, b)
        | Expr::Mod(a, b)
        | Expr::Range(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Implies(a, b)
        | Expr::Subseteq(a, b) => count_case(&a.node) + count_case(&b.node),
        Expr::Not(inner) | Expr::Neg(inner) | Expr::Prime(inner) => count_case(&inner.node),
        Expr::If(c, t, e) => count_case(&c.node) + count_case(&t.node) + count_case(&e.node),
        Expr::SetEnum(elems) | Expr::Times(elems) => {
            elems.iter().map(|e| count_case(&e.node)).sum()
        }
        Expr::Apply(f, args) => {
            count_case(&f.node) + args.iter().map(|a| count_case(&a.node)).sum::<usize>()
        }
        Expr::Forall(_, body) | Expr::Exists(_, body) => count_case(&body.node),
        _ => 0,
    }
}
