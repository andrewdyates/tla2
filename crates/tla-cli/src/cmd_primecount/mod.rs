// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 prime-count` — count primed variable references.
//!
//! For each operator, counts how many primed variable references
//! appear, identifying which operators modify state.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PrimecountOutputFormat {
    Human,
    Json,
}

pub(crate) fn cmd_primecount(
    file: &Path,
    format: PrimecountOutputFormat,
) -> Result<()> {
    let start = Instant::now();
    let source = read_source(file)?;
    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let diagnostic = tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        anyhow::bail!("lowering failed with {} error(s)", lower_result.errors.len());
    }
    let module = lower_result.module.context("lowering produced no module")?;

    let mut ops: Vec<(String, usize)> = Vec::new();
    let mut total = 0usize;
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            let count = count_primes(&def.body.node);
            total += count;
            if count > 0 {
                ops.push((def.name.node.clone(), count));
            }
        }
    }
    ops.sort_by(|a, b| b.1.cmp(&a.1));

    let elapsed = start.elapsed().as_secs_f64();
    match format {
        PrimecountOutputFormat::Human => {
            println!("prime-count: {}", file.display());
            println!("  total primed refs: {total}");
            println!("  operators with primes: {}", ops.len());
            println!();
            for (name, count) in &ops {
                println!("  {name}: {count}");
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        PrimecountOutputFormat::Json => {
            let ops_json: Vec<serde_json::Value> = ops.iter().map(|(n, c)| serde_json::json!({"name": n, "count": c})).collect();
            let output = serde_json::json!({"version":"0.1.0","file":file.display().to_string(),"total":total,"operators":ops_json,"elapsed_seconds":elapsed});
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }
    Ok(())
}

fn count_primes(expr: &Expr) -> usize {
    match expr {
        Expr::Prime(_) => 1 + match &expr { Expr::Prime(inner) => count_primes(&inner.node), _ => 0 },
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Eq(a, b) | Expr::Neq(a, b)
        | Expr::Lt(a, b) | Expr::Gt(a, b) | Expr::Leq(a, b) | Expr::Geq(a, b)
        | Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Div(a, b) | Expr::Mod(a, b)
        | Expr::Range(a, b) | Expr::In(a, b) | Expr::NotIn(a, b)
        | Expr::Implies(a, b) | Expr::Subseteq(a, b) => {
            count_primes(&a.node) + count_primes(&b.node)
        }
        Expr::Not(inner) | Expr::Neg(inner) => count_primes(&inner.node),
        Expr::If(c, t, e) => count_primes(&c.node) + count_primes(&t.node) + count_primes(&e.node),
        Expr::SetEnum(elems) | Expr::Times(elems) => elems.iter().map(|e| count_primes(&e.node)).sum(),
        Expr::Apply(f, args) => count_primes(&f.node) + args.iter().map(|a| count_primes(&a.node)).sum::<usize>(),
        Expr::Forall(_, body) | Expr::Exists(_, body) => count_primes(&body.node),
        _ => 0,
    }
}
