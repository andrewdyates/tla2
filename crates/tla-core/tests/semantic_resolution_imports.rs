// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Andrew Yates

use std::fs;
use std::path::Path;

use tempfile::TempDir;
use tla_core::ModuleLoader;

fn create_test_module(dir: &Path, name: &str, content: &str) {
    let path = dir.join(format!("{name}.tla"));
    fs::write(path, content).unwrap();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn named_instance_deps_do_not_pollute_unqualified_scope() {
    use tla_core::lower;
    use tla_core::parse_to_syntax_tree;
    use tla_core::span::FileId;
    use tla_core::{resolve_with_extends_and_instances_with_options, ResolveOptions};

    let temp = TempDir::new().unwrap();
    create_test_module(
        temp.path(),
        "N",
        r"
        ---- MODULE N ----
        CONSTANT X
        ====
    ",
    );
    create_test_module(
        temp.path(),
        "M",
        r"
        ---- MODULE M ----
        CONSTANT X
        I == INSTANCE N
        ====
    ",
    );
    create_test_module(
        temp.path(),
        "A",
        r"
        ---- MODULE A ----
        EXTENDS M
        ====
    ",
    );

    let main_file = temp.path().join("A.tla");
    let source = fs::read_to_string(&main_file).unwrap();
    let tree = parse_to_syntax_tree(&source);

    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.unwrap();

    let mut loader = ModuleLoader::new(&main_file);
    loader.seed_from_syntax_tree(&tree, &main_file);

    // Loading the EXTENDS closure also loads named-instance deps (M contains `I == INSTANCE N`).
    let deps = loader.load_extends(&module).unwrap();
    assert!(deps.contains(&"M".to_string()));
    assert!(deps.contains(&"N".to_string()));

    // Incorrect approach: treat dependency closure as EXTENDS imports (introduces duplicates).
    let wrong_exts: Vec<_> = deps
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();
    let wrong_res = resolve_with_extends_and_instances_with_options(
        &module,
        &wrong_exts,
        &[],
        ResolveOptions::model_checking(),
    );
    assert!(
        wrong_res
            .errors
            .iter()
            .any(|e| e.to_string().contains("duplicate definition")),
        "expected duplicate-definition error, got: {:?}",
        wrong_res.errors
    );

    // Correct approach: unqualified scope includes only EXTENDS modules (constants/vars/operators),
    // plus standalone INSTANCE imports (operators only).
    let (resolve_exts, resolve_insts) = loader.modules_for_semantic_resolution(&module);
    let ok_res = resolve_with_extends_and_instances_with_options(
        &module,
        &resolve_exts,
        &resolve_insts,
        ResolveOptions::model_checking(),
    );
    assert!(
        ok_res.errors.is_empty(),
        "expected no semantic errors, got: {:?}",
        ok_res.errors
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn conflicting_imported_operator_definitions_do_not_error() {
    use tla_core::lower;
    use tla_core::parse_to_syntax_tree;
    use tla_core::span::FileId;
    use tla_core::{resolve_with_extends_and_instances_with_options, ResolveOptions};

    let temp = TempDir::new().unwrap();
    create_test_module(
        temp.path(),
        "FunctionsFork",
        r"
        ---- MODULE FunctionsFork ----
        Restrict(f, S) == f
        ====
    ",
    );
    create_test_module(
        temp.path(),
        "A",
        r"
        ---- MODULE A ----
        EXTENDS Functions, FunctionsFork
        X == Restrict(1, 2)
        ====
    ",
    );

    let main_file = temp.path().join("A.tla");
    let source = fs::read_to_string(&main_file).unwrap();
    let tree = parse_to_syntax_tree(&source);

    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.unwrap();

    let mut loader = ModuleLoader::new(&main_file);
    loader.seed_from_syntax_tree(&tree, &main_file);
    let _ = loader.load_extends(&module).unwrap();

    let (resolve_exts, resolve_insts) = loader.modules_for_semantic_resolution(&module);
    let res = resolve_with_extends_and_instances_with_options(
        &module,
        &resolve_exts,
        &resolve_insts,
        ResolveOptions::model_checking(),
    );
    assert!(
        res.errors.is_empty(),
        "expected no semantic errors, got: {:?}",
        res.errors
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn modules_for_semantic_resolution_orders_transitive_extends_before_extendees() {
    use tla_core::lower;
    use tla_core::parse_to_syntax_tree;
    use tla_core::span::FileId;

    let temp = TempDir::new().unwrap();
    create_test_module(
        temp.path(),
        "N",
        r"
        ---- MODULE N ----
        F(x) == x
        ====
    ",
    );
    create_test_module(
        temp.path(),
        "M1",
        r"
        ---- MODULE M1 ----
        EXTENDS N
        ====
    ",
    );
    create_test_module(
        temp.path(),
        "M2",
        r"
        ---- MODULE M2 ----
        EXTENDS N
        ====
    ",
    );
    create_test_module(
        temp.path(),
        "A",
        r"
        ---- MODULE A ----
        EXTENDS M1, M2
        ====
    ",
    );

    let main_file = temp.path().join("A.tla");
    let source = fs::read_to_string(&main_file).unwrap();
    let tree = parse_to_syntax_tree(&source);

    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.unwrap();

    let mut loader = ModuleLoader::new(&main_file);
    loader.seed_from_syntax_tree(&tree, &main_file);
    let _ = loader.load_extends(&module).unwrap();

    let (resolve_exts, resolve_insts) = loader.modules_for_semantic_resolution(&module);
    let ext_names: Vec<_> = resolve_exts.iter().map(|m| m.name.node.as_str()).collect();
    assert_eq!(ext_names, vec!["N", "M1", "M2"]);
    assert!(resolve_insts.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn conflicting_imported_operator_definitions_with_different_arity_are_errors() {
    use tla_core::lower;
    use tla_core::parse_to_syntax_tree;
    use tla_core::span::FileId;
    use tla_core::{
        resolve_with_extends_and_instances_with_options, ResolveErrorKind, ResolveOptions,
    };

    let temp = TempDir::new().unwrap();
    create_test_module(
        temp.path(),
        "M1",
        r"
        ---- MODULE M1 ----
        F(x) == x
        ====
    ",
    );
    create_test_module(
        temp.path(),
        "M2",
        r"
        ---- MODULE M2 ----
        F(x, y) == x
        ====
    ",
    );
    create_test_module(
        temp.path(),
        "A",
        r"
        ---- MODULE A ----
        EXTENDS M1, M2
        ====
    ",
    );

    let main_file = temp.path().join("A.tla");
    let source = fs::read_to_string(&main_file).unwrap();
    let tree = parse_to_syntax_tree(&source);

    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.unwrap();

    let mut loader = ModuleLoader::new(&main_file);
    loader.seed_from_syntax_tree(&tree, &main_file);
    let _ = loader.load_extends(&module).unwrap();

    let (resolve_exts, resolve_insts) = loader.modules_for_semantic_resolution(&module);
    let res = resolve_with_extends_and_instances_with_options(
        &module,
        &resolve_exts,
        &resolve_insts,
        ResolveOptions::model_checking(),
    );

    assert!(
        res.errors.iter().any(|e| matches!(
            e.kind,
            ResolveErrorKind::ImportedOperatorArityConflict {
                ref name,
                first_arity: 1,
                second_arity: 2,
                ..
            } if name == "F"
        )),
        "expected arity-conflict error for F(1) vs F(2), got: {:?}",
        res.errors
    );
}
