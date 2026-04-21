// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extract unchanged variables from UNCHANGED expressions.
//!
//! Split from `guard_check.rs` for file-size hygiene (Part of #3427).

use std::sync::Arc;

use tla_core::ast::Expr;

use crate::eval::EvalCtx;
use crate::var_index::VarRegistry;

use super::SymbolicAssignment;

/// Extract unchanged variables from an UNCHANGED expression.
///
/// When `ctx` is provided, resolves definition aliases (e.g., `vars == <<x, y>>`)
/// from extended modules. This fixes #124 where definitions from EXTENDS are
/// not recognized as variable aliases.
pub(super) fn extract_unchanged_vars_symbolic_with_ctx(
    expr: &Expr,
    vars: &[Arc<str>],
    assignments: &mut Vec<SymbolicAssignment>,
    ctx: Option<&EvalCtx>,
    registry: &VarRegistry,
) {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            // O(1) variable lookup via registry
            let found = registry.get(name.as_str()).map(|idx| &vars[idx.as_usize()]);
            if let Some(var) = found {
                assignments.push(SymbolicAssignment::Unchanged(Arc::clone(var)));
            } else if let Some(ctx) = ctx {
                // Not a state variable - check if it's a definition alias (e.g., vars == <<x, y>>)
                // This handles definitions from EXTENDS modules (#124)
                if let Some(def) = ctx.get_op(name.as_str()) {
                    // Recursively extract from the definition body
                    extract_unchanged_vars_symbolic_with_ctx(
                        &def.body.node,
                        vars,
                        assignments,
                        Some(ctx),
                        registry,
                    );
                }
            }
        }
        Expr::Tuple(elems) => {
            for elem in elems {
                extract_unchanged_vars_symbolic_with_ctx(
                    &elem.node,
                    vars,
                    assignments,
                    ctx,
                    registry,
                );
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::parse_module;
    use tla_core::name_intern::NameId;
    use tla_core::Spanned;

    fn arc(s: &str) -> Arc<str> {
        Arc::from(s)
    }

    fn registry_from(vars: &[Arc<str>]) -> VarRegistry {
        VarRegistry::from_names(vars.iter().cloned())
    }

    #[test]
    fn test_extract_unchanged_statevar_node() {
        // StateVar node should be recognized as an unchanged variable
        // This is the fix from 51950ec5 — using StateVar instead of Ident
        let vars: Vec<Arc<str>> = vec![arc("x"), arc("y")];
        let registry = registry_from(&vars);
        let mut assignments = Vec::new();

        let expr = Expr::StateVar("x".to_string(), 0, NameId(0));
        extract_unchanged_vars_symbolic_with_ctx(&expr, &vars, &mut assignments, None, &registry);

        assert_eq!(assignments.len(), 1);
        match &assignments[0] {
            SymbolicAssignment::Unchanged(name) => assert_eq!(name.as_ref(), "x"),
            other => panic!("expected Unchanged, got {:?}", other),
        }
    }

    #[test]
    fn test_extract_unchanged_ident_node() {
        // Ident node should also work (pre-existing behavior)
        let vars: Vec<Arc<str>> = vec![arc("x"), arc("y")];
        let registry = registry_from(&vars);
        let mut assignments = Vec::new();

        let expr = Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID);
        extract_unchanged_vars_symbolic_with_ctx(&expr, &vars, &mut assignments, None, &registry);

        assert_eq!(assignments.len(), 1);
        match &assignments[0] {
            SymbolicAssignment::Unchanged(name) => assert_eq!(name.as_ref(), "y"),
            other => panic!("expected Unchanged, got {:?}", other),
        }
    }

    #[test]
    fn test_extract_unchanged_tuple_with_statevar() {
        // Tuple of StateVar nodes should extract all unchanged variables
        let vars: Vec<Arc<str>> = vec![arc("x"), arc("y"), arc("z")];
        let registry = registry_from(&vars);
        let mut assignments = Vec::new();

        let expr = Expr::Tuple(vec![
            Spanned::dummy(Expr::StateVar("x".to_string(), 0, NameId(0))),
            Spanned::dummy(Expr::StateVar("z".to_string(), 2, NameId(2))),
        ]);
        extract_unchanged_vars_symbolic_with_ctx(&expr, &vars, &mut assignments, None, &registry);

        assert_eq!(assignments.len(), 2);
        match &assignments[0] {
            SymbolicAssignment::Unchanged(name) => assert_eq!(name.as_ref(), "x"),
            other => panic!("expected Unchanged(x), got {:?}", other),
        }
        match &assignments[1] {
            SymbolicAssignment::Unchanged(name) => assert_eq!(name.as_ref(), "z"),
            other => panic!("expected Unchanged(z), got {:?}", other),
        }
    }

    #[test]
    fn test_extract_unchanged_definition_alias_with_ctx() {
        // Definition alias should be expanded through ctx.get_op(), then tuple elements extracted.
        let vars: Vec<Arc<str>> = vec![arc("x"), arc("y")];
        let registry = registry_from(&vars);
        let mut assignments = Vec::new();
        let module = parse_module(
            r#"
---- MODULE AliasVars ----
VARIABLES x, y
vars == <<x, y>>
====
"#,
        );

        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);

        let expr = Expr::Ident("vars".to_string(), tla_core::name_intern::NameId::INVALID);
        extract_unchanged_vars_symbolic_with_ctx(
            &expr,
            &vars,
            &mut assignments,
            Some(&ctx),
            &registry,
        );

        assert_eq!(assignments.len(), 2);
        match &assignments[0] {
            SymbolicAssignment::Unchanged(name) => assert_eq!(name.as_ref(), "x"),
            other => panic!("expected Unchanged(x), got {:?}", other),
        }
        match &assignments[1] {
            SymbolicAssignment::Unchanged(name) => assert_eq!(name.as_ref(), "y"),
            other => panic!("expected Unchanged(y), got {:?}", other),
        }
    }

    #[test]
    fn test_extract_unchanged_non_var_ident_without_ctx() {
        // An Ident that is not a state variable and no ctx — should produce nothing
        let vars: Vec<Arc<str>> = vec![arc("x"), arc("y")];
        let registry = registry_from(&vars);
        let mut assignments = Vec::new();

        let expr = Expr::Ident(
            "notavar".to_string(),
            tla_core::name_intern::NameId::INVALID,
        );
        extract_unchanged_vars_symbolic_with_ctx(&expr, &vars, &mut assignments, None, &registry);

        assert_eq!(assignments.len(), 0);
    }

    #[test]
    fn test_extract_unchanged_non_var_statevar_without_ctx() {
        // A StateVar whose name isn't in vars — should produce nothing
        let vars: Vec<Arc<str>> = vec![arc("x"), arc("y")];
        let registry = registry_from(&vars);
        let mut assignments = Vec::new();

        let expr = Expr::StateVar("notavar".to_string(), 99, NameId(99));
        extract_unchanged_vars_symbolic_with_ctx(&expr, &vars, &mut assignments, None, &registry);

        assert_eq!(assignments.len(), 0);
    }
}
