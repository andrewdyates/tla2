// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 temporal-ops` — count temporal operator usage.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TemporalopsOutputFormat { Human, Json }

pub(crate) fn cmd_temporalops(file: &Path, format: TemporalopsOutputFormat) -> Result<()> {
    let start = Instant::now();
    let source = read_source(file)?;
    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        let fp = file.display().to_string();
        for err in &lower_result.errors {
            tla_core::lower_error_diagnostic(&fp, &err.message, err.span).eprint(&fp, &source);
        }
        bail!("lowering failed with {} error(s)", lower_result.errors.len());
    }
    let module = lower_result.module.context("lowering produced no module")?;

    let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            count_temporal(&def.body.node, &mut counts);
        }
    }
    let total: usize = counts.values().sum();
    let elapsed = start.elapsed().as_secs_f64();

    match format {
        TemporalopsOutputFormat::Human => {
            println!("temporal-ops: {}", file.display());
            println!("  total temporal operators: {total}");
            for (op, c) in &counts { println!("  {op:20} {c}"); }
            println!("\n  elapsed: {elapsed:.2}s");
        }
        TemporalopsOutputFormat::Json => {
            let output = serde_json::json!({"version":"0.1.0","file":file.display().to_string(),"total":total,"operations":counts,"elapsed_seconds":elapsed});
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }
    Ok(())
}

fn count_temporal(expr: &Expr, counts: &mut BTreeMap<&'static str, usize>) {
    match expr {
        Expr::Always(inner) => { *counts.entry("[]").or_insert(0) += 1; count_temporal(&inner.node, counts); }
        Expr::Eventually(inner) => { *counts.entry("<>").or_insert(0) += 1; count_temporal(&inner.node, counts); }
        Expr::LeadsTo(a, b) => { *counts.entry("~>").or_insert(0) += 1; count_temporal(&a.node, counts); count_temporal(&b.node, counts); }
        Expr::WeakFair(a, b) => { *counts.entry("WF_").or_insert(0) += 1; count_temporal(&a.node, counts); count_temporal(&b.node, counts); }
        Expr::StrongFair(a, b) => { *counts.entry("SF_").or_insert(0) += 1; count_temporal(&a.node, counts); count_temporal(&b.node, counts); }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b) => { count_temporal(&a.node, counts); count_temporal(&b.node, counts); }
        Expr::Not(inner) => count_temporal(&inner.node, counts),
        Expr::If(c, t, e) => { count_temporal(&c.node, counts); count_temporal(&t.node, counts); count_temporal(&e.node, counts); }
        _ => {}
    }
}
