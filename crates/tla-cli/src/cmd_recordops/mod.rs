// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 record-ops` — count record/function operations.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RecordopsOutputFormat {
    Human,
    Json,
}

pub(crate) fn cmd_recordops(file: &Path, format: RecordopsOutputFormat) -> Result<()> {
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
        bail!("lowering failed with {} error(s)", lower_result.errors.len());
    }
    let module = lower_result.module.context("lowering produced no module")?;

    let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            count_record_ops(&def.body.node, &mut counts);
        }
    }
    let total: usize = counts.values().sum();
    let elapsed = start.elapsed().as_secs_f64();

    match format {
        RecordopsOutputFormat::Human => {
            println!("record-ops: {}", file.display());
            println!("  total record/function ops: {total}");
            println!();
            let mut sorted: Vec<_> = counts.iter().collect();
            sorted.sort_by(|a, b| b.1.cmp(a.1));
            for (op, count) in &sorted {
                println!("  {op:20} {count}");
            }
            println!("\n  elapsed: {elapsed:.2}s");
        }
        RecordopsOutputFormat::Json => {
            let output = serde_json::json!({"version":"0.1.0","file":file.display().to_string(),"total":total,"operations":counts,"elapsed_seconds":elapsed});
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }
    Ok(())
}

fn count_record_ops(expr: &Expr, counts: &mut BTreeMap<&'static str, usize>) {
    match expr {
        Expr::Record(_) => { *counts.entry("Record").or_insert(0) += 1; }
        Expr::RecordSet(_) => { *counts.entry("RecordSet").or_insert(0) += 1; }
        Expr::RecordAccess(inner, _) => {
            *counts.entry("RecordAccess").or_insert(0) += 1;
            count_record_ops(&inner.node, counts);
        }
        Expr::FuncApply(f, arg) => {
            *counts.entry("FuncApply").or_insert(0) += 1;
            count_record_ops(&f.node, counts);
            count_record_ops(&arg.node, counts);
        }
        Expr::Except(base, updates) => {
            *counts.entry("EXCEPT").or_insert(0) += 1;
            count_record_ops(&base.node, counts);
            for u in updates {
                count_record_ops(&u.value.node, counts);
            }
        }
        Expr::FuncSet(a, b) => {
            *counts.entry("FuncSet").or_insert(0) += 1;
            count_record_ops(&a.node, counts);
            count_record_ops(&b.node, counts);
        }
        // Recurse through other expressions.
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Eq(a, b) | Expr::Neq(a, b)
        | Expr::Lt(a, b) | Expr::Gt(a, b) | Expr::Leq(a, b) | Expr::Geq(a, b)
        | Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Div(a, b) | Expr::Mod(a, b)
        | Expr::Range(a, b) | Expr::In(a, b) | Expr::NotIn(a, b)
        | Expr::Implies(a, b) | Expr::Subseteq(a, b) => {
            count_record_ops(&a.node, counts);
            count_record_ops(&b.node, counts);
        }
        Expr::Not(inner) | Expr::Neg(inner) | Expr::Prime(inner) => count_record_ops(&inner.node, counts),
        Expr::If(c, t, e) => {
            count_record_ops(&c.node, counts);
            count_record_ops(&t.node, counts);
            count_record_ops(&e.node, counts);
        }
        Expr::SetEnum(elems) | Expr::Times(elems) => {
            for e in elems { count_record_ops(&e.node, counts); }
        }
        Expr::Apply(f, args) => {
            count_record_ops(&f.node, counts);
            for a in args { count_record_ops(&a.node, counts); }
        }
        Expr::Forall(_, body) | Expr::Exists(_, body) => count_record_ops(&body.node, counts),
        _ => {}
    }
}
