// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::ast::{Expr, Module, Unit};
use crate::expr_contains_primed_param_v;

/// Compute `has_primed_param` for all operators in a module (#2662).
///
/// For each operator with parameters, checks whether any parameter name appears
/// primed in the body. This is a local check (no transitive propagation needed)
/// because it only examines the operator's own parameters vs its own body.
///
/// Must be called after lowering. Replaces the per-call AST walk in
/// `eval::helpers::apply.rs` with a one-time parse-time computation.
pub fn compute_has_primed_param(module: &mut Module) {
    for unit in &mut module.units {
        if let Unit::Operator(def) = &mut unit.node {
            def.has_primed_param = operator_has_primed_param(&def.params, &def.body.node);
        }
    }
}

/// Check if any parameter name appears primed in an operator body.
/// Exported for use by `eval_module_load` when constructing operator defs
/// outside the normal module parse path.
pub fn operator_has_primed_param(params: &[crate::ast::OpParam], body: &Expr) -> bool {
    params
        .iter()
        .any(|param| expr_contains_primed_param_v(body, &param.name.node))
}
