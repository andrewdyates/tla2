// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for parallel checker module resolution and variable/operator collection.
//!
//! Part of #810: The parallel checker constructor now uses
//! `checker_setup::setup_checker_modules` directly. This module retains
//! tests that exercise the shared `checker_ops::collect_ops_vars_and_assumes`
//! function via a thin test-only wrapper.

#[cfg(test)]
use super::*;

/// Collect operator definitions, state variables, and ASSUME formulas from
/// the module graph in a single pass.
///
/// Thin test-only wrapper around `crate::checker_ops::collect_ops_vars_and_assumes`.
#[cfg(test)]
#[allow(clippy::type_complexity)]
fn collect_vars_ops_and_assumes(
    main_module: &Module,
    extended_modules: &[Module],
    unqualified_modules: &FxHashSet<String>,
    variable_contributing_modules: &FxHashSet<String>,
) -> (
    Vec<Arc<str>>,
    FxHashMap<String, OperatorDef>,
    Vec<(String, Spanned<Expr>)>,
) {
    let ext_refs: Vec<&Module> = extended_modules.iter().collect();
    crate::checker_ops::collect_ops_vars_and_assumes(
        main_module,
        &ext_refs,
        |name| unqualified_modules.contains(name),
        |name| variable_contributing_modules.contains(name),
    )
}

/// Collect variable names and operator definitions (without ASSUMEs).
#[cfg(test)]
fn collect_vars_and_ops(
    main_module: &Module,
    extended_modules: &[Module],
    unqualified_modules: &FxHashSet<String>,
    variable_contributing_modules: &FxHashSet<String>,
) -> (Vec<Arc<str>>, FxHashMap<String, OperatorDef>) {
    let (vars, op_defs, _assumes) = collect_vars_ops_and_assumes(
        main_module,
        extended_modules,
        unqualified_modules,
        variable_contributing_modules,
    );
    (vars, op_defs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::ast::{OperatorDef, Unit};
    use tla_core::Span;

    fn s(name: &str) -> Spanned<String> {
        Spanned::dummy(name.to_string())
    }

    fn make_module(name: &str, extends: &[&str], units: Vec<Spanned<Unit>>) -> Module {
        Module {
            name: s(name),
            extends: extends.iter().map(|e| s(e)).collect(),
            units,
            action_subscript_spans: Default::default(),
            span: Span::dummy(),
        }
    }

    fn var_unit(names: &[&str]) -> Spanned<Unit> {
        Spanned::dummy(Unit::Variable(names.iter().map(|n| s(n)).collect()))
    }

    fn op_unit(name: &str) -> Spanned<Unit> {
        Spanned::dummy(Unit::Operator(OperatorDef {
            name: s(name),
            params: vec![],
            body: Spanned::dummy(Expr::Bool(true)),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }))
    }

    /// #2787: When an EXTENDS'd module declares both `VARIABLE x` and operator
    /// `x == ...`, the variable should be skipped (implicit constant binding).
    /// The parallel path previously used a single-pass approach that missed this.
    #[test]
    fn implicit_binding_skip_excludes_operator_shadowed_variable() {
        // Extended module declares VARIABLE x AND operator x (implicit binding)
        let ext = make_module("Base", &[], vec![var_unit(&["x", "y"]), op_unit("x")]);

        let main = make_module("Main", &["Base"], vec![var_unit(&["z"])]);

        let unqualified: FxHashSet<String> = ["Base".to_string()].into_iter().collect();
        let var_contributing: FxHashSet<String> = ["Base".to_string()].into_iter().collect();

        let (vars, op_defs) = collect_vars_and_ops(&main, &[ext], &unqualified, &var_contributing);

        // x should be skipped (operator shadows it), y and z should remain
        let var_names: Vec<&str> = vars.iter().map(std::convert::AsRef::as_ref).collect();
        assert!(
            !var_names.contains(&"x"),
            "x should be excluded by implicit-binding skip, got: {var_names:?}"
        );
        assert!(
            var_names.contains(&"y"),
            "y should be included, got: {var_names:?}"
        );
        assert!(
            var_names.contains(&"z"),
            "z (main module var) should be included, got: {var_names:?}"
        );
        assert!(
            op_defs.contains_key("x"),
            "x should exist as operator definition"
        );
    }

    /// Verify that operator definitions from the main module also gate variable
    /// collection from extended modules (main-module operator shadows extended variable).
    #[test]
    fn main_module_operator_shadows_extended_variable() {
        let ext = make_module("Base", &[], vec![var_unit(&["a", "b"])]);

        // Main module defines operator "a", which should shadow Base's VARIABLE a
        let main = make_module("Main", &["Base"], vec![op_unit("a"), var_unit(&["c"])]);

        let unqualified: FxHashSet<String> = ["Base".to_string()].into_iter().collect();
        let var_contributing: FxHashSet<String> = ["Base".to_string()].into_iter().collect();

        let (vars, _op_defs) = collect_vars_and_ops(&main, &[ext], &unqualified, &var_contributing);

        let var_names: Vec<&str> = vars.iter().map(std::convert::AsRef::as_ref).collect();
        assert!(
            !var_names.contains(&"a"),
            "a should be excluded (main module operator shadows it), got: {var_names:?}"
        );
        assert!(
            var_names.contains(&"b"),
            "b should be included, got: {var_names:?}"
        );
        assert!(
            var_names.contains(&"c"),
            "c (main module var) should be included, got: {var_names:?}"
        );
    }

    /// Without implicit binding, all variables from EXTENDS'd modules are collected.
    #[test]
    fn no_implicit_binding_collects_all_variables() {
        let ext = make_module("Base", &[], vec![var_unit(&["a", "b"])]);
        let main = make_module("Main", &["Base"], vec![var_unit(&["c"])]);

        let unqualified: FxHashSet<String> = ["Base".to_string()].into_iter().collect();
        let var_contributing: FxHashSet<String> = ["Base".to_string()].into_iter().collect();

        let (vars, _op_defs) = collect_vars_and_ops(&main, &[ext], &unqualified, &var_contributing);

        let var_names: Vec<&str> = vars.iter().map(std::convert::AsRef::as_ref).collect();
        assert_eq!(
            var_names.len(),
            3,
            "expected 3 variables, got: {var_names:?}"
        );
        assert!(var_names.contains(&"a"));
        assert!(var_names.contains(&"b"));
        assert!(var_names.contains(&"c"));
    }

    /// Variables from non-variable-contributing modules (INSTANCE, not EXTENDS)
    /// should not be collected regardless of operator shadowing.
    #[test]
    fn instance_module_variables_not_collected() {
        let inst_mod = make_module("Instanced", &[], vec![var_unit(&["x", "y"]), op_unit("z")]);
        let main = make_module("Main", &[], vec![var_unit(&["a"])]);

        // Module is in unqualified set (operators imported) but NOT in var_contributing
        let unqualified: FxHashSet<String> = ["Instanced".to_string()].into_iter().collect();
        let var_contributing: FxHashSet<String> = FxHashSet::default(); // empty: no EXTENDS

        let (vars, op_defs) =
            collect_vars_and_ops(&main, &[inst_mod], &unqualified, &var_contributing);

        let var_names: Vec<&str> = vars.iter().map(std::convert::AsRef::as_ref).collect();
        assert_eq!(
            var_names,
            vec!["a"],
            "only main module var should be collected, got: {var_names:?}"
        );
        assert!(
            op_defs.contains_key("z"),
            "operators from unqualified module should still be collected"
        );
    }
}
