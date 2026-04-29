// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SequencesExt operator tests — split from monolithic sequences_ext.rs (973 lines)

use tla_check::Value;
use tla_core::{lower, parse_to_syntax_tree, FileId};

use super::helpers::{eval_str, int_set, int_set_of_seqs, sorted_set_from_values};

mod core_ops;
mod fold_prefix;
mod prefix_suffix;
mod transforms;

/// Eval helper that wraps expression in a module with EXTENDS Sequences, SequencesExt.
pub(super) fn eval_seqext_str(expr: &str) -> Result<Value, String> {
    let module_src = format!(
        "---- MODULE Test ----\nEXTENDS Sequences, SequencesExt\n\nOp == {}\n\n====",
        expr
    );
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = match lower_result.module {
        Some(m) => m,
        None => return Err(format!("Parse error: {:?}", lower_result.errors)),
    };

    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let ctx = tla_check::EvalCtx::new();
                return tla_check::eval(&ctx, &def.body).map_err(|e| format!("{:?}", e));
            }
        }
    }
    Err("Op not found".to_string())
}
