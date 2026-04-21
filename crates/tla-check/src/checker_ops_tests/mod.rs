// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `crate::checker_ops`.

use super::*;
use crate::eval::EvalCtx;
use crate::state::ArrayState;
use rustc_hash::FxHashMap;

mod invariant_checks;
mod property_classify;
mod property_classify_instance;
mod property_tautology;
mod temporal_gaps;

/// Parse a TLA+ source and produce an EvalCtx + op_defs FxHashMap suitable
/// for `classify_property_safety_parts` and `check_property_tautologies`.
fn setup_for_classification(
    src: &str,
) -> (FxHashMap<String, tla_core::ast::OperatorDef>, EvalCtx, String) {
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut op_defs: FxHashMap<String, tla_core::ast::OperatorDef> = FxHashMap::default();
    for unit in &module.units {
        match &unit.node {
            tla_core::ast::Unit::Variable(var_names) => {
                for var in var_names {
                    ctx.register_var(Arc::from(var.node.as_str()));
                }
            }
            tla_core::ast::Unit::Operator(def) => {
                op_defs.insert(def.name.node.clone(), def.clone());
            }
            _ => {}
        }
    }

    let root_name = module.name.node.clone();
    (op_defs, ctx, root_name)
}
