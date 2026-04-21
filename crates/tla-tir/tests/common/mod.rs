// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(dead_code)]

use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};
use tla_core::ast::Unit;
use tla_core::{lower, parse_to_syntax_tree, FileId, ModuleLoader, Spanned};
use tla_tir::{
    lower_expr, lower_expr_with_env, lower_module_with_env, TirExpr, TirLowerError, TirLoweringEnv,
    TirModule, TirNameKind,
};
use tla_value::{val_false, val_true};

pub(crate) fn lower_named_operator(source: &str, name: &str) -> Spanned<TirExpr> {
    let tree = parse_to_syntax_tree(source);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("lower produced no module");
    let def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node.as_str() == name => Some(def),
            _ => None,
        })
        .expect("missing operator");

    lower_expr(&module, &def.body).expect("TIR lowering should succeed")
}

pub(crate) fn lower_named_operator_result(
    source: &str,
    name: &str,
) -> Result<Spanned<TirExpr>, TirLowerError> {
    let tree = parse_to_syntax_tree(source);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("lower produced no module");
    let def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node.as_str() == name => Some(def),
            _ => None,
        })
        .expect("missing operator");

    lower_expr(&module, &def.body)
}

pub(crate) fn lower_named_operator_with_env(
    source: &str,
    extra_modules: &[&str],
    name: &str,
) -> Spanned<TirExpr> {
    let temp = TempSpecDir::new();
    let main_path = temp.write_main(source);
    let mut loader = ModuleLoader::new(&main_path);
    loader.load("Main").expect("load Main");

    let main = &loader.get("Main").expect("missing Main").module;
    let def = main
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node.as_str() == name => Some(def),
            _ => None,
        })
        .expect("missing operator");

    let mut env = TirLoweringEnv::new(main);
    for module_name in extra_modules {
        let module = &loader
            .get(module_name)
            .unwrap_or_else(|| panic!("missing module {module_name}"))
            .module;
        env.add_module(module);
    }

    lower_expr_with_env(&env, main, &def.body).expect("TIR lowering should succeed")
}

pub(crate) fn lower_main_module_with_env(source: &str, extra_modules: &[&str]) -> TirModule {
    let temp = TempSpecDir::new();
    let main_path = temp.write_main(source);
    let mut loader = ModuleLoader::new(&main_path);
    loader.load("Main").expect("load Main");

    let main = &loader.get("Main").expect("missing Main").module;
    let mut env = TirLoweringEnv::new(main);
    for module_name in extra_modules {
        let module = &loader
            .get(module_name)
            .unwrap_or_else(|| panic!("missing module {module_name}"))
            .module;
        env.add_module(module);
    }

    lower_module_with_env(&env, main).expect("module lowering should succeed")
}

pub(crate) fn expect_ident(expr: &Spanned<TirExpr>, expected: &str) {
    match &expr.node {
        TirExpr::Name(name) => {
            assert_eq!(name.name, expected);
            assert_eq!(name.kind, TirNameKind::Ident);
        }
        other => panic!("expected ident {expected}, got {other:?}"),
    }
}

pub(crate) fn expect_name(expr: &Spanned<TirExpr>, expected: &str) {
    match &expr.node {
        TirExpr::Name(name) => assert_eq!(name.name, expected),
        other => panic!("expected name {expected}, got {other:?}"),
    }
}

pub(crate) fn expect_bool_const(expr: &Spanned<TirExpr>, expected: bool) {
    match &expr.node {
        TirExpr::Const { value, .. } => {
            let expected = if expected { val_true() } else { val_false() };
            assert_eq!(*value, expected);
        }
        other => panic!("expected bool const {expected}, got {other:?}"),
    }
}

pub(crate) fn expect_int_const(expr: &Spanned<TirExpr>, expected: i64) {
    match &expr.node {
        TirExpr::Const { value, .. } => assert_eq!(value.to_string(), expected.to_string()),
        other => panic!("expected int const {expected}, got {other:?}"),
    }
}

#[derive(Debug)]
struct TempSpecDir {
    path: PathBuf,
}

impl TempSpecDir {
    fn new() -> Self {
        let unique = format!(
            "tla_tir_lowering_{}_{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system clock before unix epoch")
                .as_nanos()
        );
        let path = std::env::temp_dir().join(unique);
        fs::create_dir_all(&path).expect("create temp spec dir");
        Self { path }
    }

    fn write_main(&self, source: &str) -> PathBuf {
        let main_path = self.path.join("Main.tla");
        fs::write(&main_path, source).expect("write Main.tla");
        main_path
    }
}

impl Drop for TempSpecDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

pub(crate) fn instance_source() -> &'static str {
    r"
---- MODULE Main ----
I == INSTANCE Inner WITH Flag <- TRUE
P(x) == INSTANCE Inner WITH Flag <- x
Bridge == INSTANCE Mid WITH Flag <- TRUE
Named == I!Safe
Param == P(FALSE)!Safe
Chain == Bridge!LeafInst!Safe
====
---- MODULE Inner ----
Flag == FALSE
Safe == Flag
====
---- MODULE Mid ----
Flag == FALSE
LeafInst == INSTANCE Leaf WITH Flag <- Flag
====
---- MODULE Leaf ----
Flag == FALSE
Safe == Flag
===="
}
