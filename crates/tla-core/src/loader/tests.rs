// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::error::LoadError;
use super::ModuleLoader;
use std::fs;
use std::path::{Path, PathBuf};
use tempfile::TempDir;

fn create_test_module(dir: &Path, name: &str, content: &str) {
    let path = dir.join(format!("{name}.tla"));
    fs::write(path, content).unwrap();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_module_in_base_dir() {
    let temp = TempDir::new().unwrap();
    create_test_module(
        temp.path(),
        "Voting",
        r"
            ---- MODULE Voting ----
            VARIABLE votes
            ====
        ",
    );

    let main_file = temp.path().join("Main.tla");
    let loader = ModuleLoader::new(&main_file);

    let path = loader.find_module("Voting").unwrap();
    assert!(path.ends_with("Voting.tla"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_module_not_found() {
    let temp = TempDir::new().unwrap();
    let main_file = temp.path().join("Main.tla");
    let loader = ModuleLoader::new(&main_file);

    let result = loader.find_module("NonExistent");
    assert!(matches!(result, Err(LoadError::NotFound { .. })));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_module() {
    let temp = TempDir::new().unwrap();
    create_test_module(
        temp.path(),
        "Voting",
        r"
            ---- MODULE Voting ----
            VARIABLE votes
            Init == votes = 0
            ====
        ",
    );

    let main_file = temp.path().join("Main.tla");
    let mut loader = ModuleLoader::new(&main_file);

    let loaded = loader.load("Voting").unwrap();
    assert_eq!(loaded.module.name.node, "Voting");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_module_caching() {
    let temp = TempDir::new().unwrap();
    create_test_module(
        temp.path(),
        "Voting",
        r"
            ---- MODULE Voting ----
            VARIABLE votes
            ====
        ",
    );

    let main_file = temp.path().join("Main.tla");
    let mut loader = ModuleLoader::new(&main_file);

    // Load twice - should use cache
    let _ = loader.load("Voting").unwrap();
    let _ = loader.load("Voting").unwrap();

    // Only one entry in cache
    assert_eq!(loader.cache.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_modules_for_model_checking_prefix_and_remainder_ordering() {
    let temp = TempDir::new().unwrap();

    create_test_module(
        temp.path(),
        "Foo",
        r"
            ---- MODULE Foo ----
            foo == 1
            ====
        ",
    );
    create_test_module(
        temp.path(),
        "Bar",
        r"
            ---- MODULE Bar ----
            bar == 1
            ====
        ",
    );
    create_test_module(
        temp.path(),
        "Baz",
        r"
            ---- MODULE Baz ----
            baz == 1
            ====
        ",
    );
    create_test_module(
        temp.path(),
        "Qux",
        r"
            ---- MODULE Qux ----
            qux == 1
            ====
        ",
    );
    create_test_module(
        temp.path(),
        "Main",
        r"
            ---- MODULE Main ----
            EXTENDS Foo
            INSTANCE Bar
            I == INSTANCE Baz
            J == LET K == INSTANCE Qux IN K!qux
            ====
        ",
    );

    let main_file = temp.path().join("Main.tla");
    let mut loader = ModuleLoader::new(&main_file);

    let main = loader.load("Main").unwrap().module.clone();
    let _ = loader.load_extends(&main).unwrap();
    let _ = loader.load_instances(&main).unwrap();

    let modules = loader.modules_for_model_checking(&main);
    let names: Vec<_> = modules.iter().map(|m| m.name.node.as_str()).collect();

    assert_eq!(names, vec!["Foo", "Bar", "Baz", "Qux"]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_inline_submodule() {
    let temp = TempDir::new().unwrap();
    create_test_module(
        temp.path(),
        "Synod",
        r"
            ---- MODULE Synod ----
            EXTENDS Naturals

            CONSTANTS N, Inputs
            Proc == 1..N

            ---- MODULE Inner ----
            VARIABLES chosen
            IInit == chosen = CHOOSE x : x \in Inputs
            ====

            IS(chosen) == INSTANCE Inner
            Spec == \EE chosen : IS(chosen)!IInit
            ====
        ",
    );

    let main_file = temp.path().join("Main.tla");
    let mut loader = ModuleLoader::new(&main_file);

    let _ = loader.load("Synod").unwrap();

    let inner = loader
        .get("Inner")
        .expect("Inner submodule should be cached");
    assert_eq!(inner.module.name.node, "Inner");
    assert_eq!(loader.cache.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seed_from_syntax_tree_for_extends() {
    // Test that seed_from_syntax_tree enables EXTENDS to resolve inline modules.
    // This is the pattern used by BufferedRandomAccessFile.tla which defines
    // Common and RandomAccessFile as inline modules, then does EXTENDS Common.
    let temp = TempDir::new().unwrap();
    create_test_module(
        temp.path(),
        "Main",
        r"
            ---- MODULE Main ----
            EXTENDS Common
            VARIABLES x
            Init == Common!Helper(x)
            ====

            ---- MODULE Common ----
            Helper(v) == v \in {1,2,3}
            ====
        ",
    );

    let main_file = temp.path().join("Main.tla");
    let source = fs::read_to_string(&main_file).unwrap();
    let tree = crate::syntax::parse_to_syntax_tree(&source);

    let mut loader = ModuleLoader::new(&main_file);

    // Before seeding, Common is not in cache
    assert!(loader.get("Common").is_none());

    // Seed from syntax tree
    loader.seed_from_syntax_tree(&tree, &main_file);

    // Now Common should be in cache
    let common = loader
        .get("Common")
        .expect("Common should be cached after seeding");
    assert_eq!(common.module.name.node, "Common");

    // Main is also cached
    let main = loader.get("Main").expect("Main should also be cached");
    assert_eq!(main.module.name.node, "Main");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_stdlib() {
    let loader = ModuleLoader::with_base_dir(PathBuf::from("."));

    assert!(loader.is_stdlib("Naturals"));
    assert!(loader.is_stdlib("Integers"));
    assert!(loader.is_stdlib("Sequences"));
    assert!(!loader.is_stdlib("Voting"));
    assert!(!loader.is_stdlib("MyModule"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_instances_nested_instance_expr_order_is_deterministic() {
    let temp = TempDir::new().unwrap();
    create_test_module(
        temp.path(),
        "ModA",
        r"
            ---- MODULE ModA ----
            Foo == TRUE
            ====
        ",
    );
    create_test_module(
        temp.path(),
        "ModB",
        r"
            ---- MODULE ModB ----
            Bar == TRUE
            ====
        ",
    );
    create_test_module(
        temp.path(),
        "ModC",
        r"
            ---- MODULE ModC ----
            Baz == TRUE
            ====
        ",
    );
    create_test_module(
        temp.path(),
        "Main",
        r"
            ---- MODULE Main ----
            Op == LET A == INSTANCE ModA
                      B == INSTANCE ModB
                      C == INSTANCE ModC
                  IN TRUE
            ====
        ",
    );

    let main_file = temp.path().join("Main.tla");
    let expected = vec!["ModA".to_string(), "ModB".to_string(), "ModC".to_string()];

    // Create fresh loaders to ensure we don't depend on HashMap/HashSet iteration order or
    // hasher seeding across instances.
    for _ in 0..10 {
        let mut loader = ModuleLoader::new(&main_file);
        let _ = loader.load("Main").unwrap();
        let main = loader.get("Main").unwrap().module.clone();
        let instances = loader.load_instances(&main).unwrap();
        assert_eq!(instances, expected);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_instances_scans_instance_substitutions_for_nested_instances() {
    let temp = TempDir::new().unwrap();
    create_test_module(
        temp.path(),
        "ModA",
        r"
            ---- MODULE ModA ----
            Foo == TRUE
            ====
        ",
    );
    create_test_module(
        temp.path(),
        "ModB",
        r"
            ---- MODULE ModB ----
            Bar == TRUE
            ====
        ",
    );
    create_test_module(
        temp.path(),
        "Main",
        r"
            ---- MODULE Main ----
            INSTANCE ModA WITH Foo <- (LET B == INSTANCE ModB IN TRUE)
            ====
        ",
    );

    let main_file = temp.path().join("Main.tla");
    let mut loader = ModuleLoader::new(&main_file);
    let _ = loader.load("Main").unwrap();
    let main = loader.get("Main").unwrap().module.clone();
    let instances = loader.load_instances(&main).unwrap();
    assert_eq!(instances, vec!["ModA".to_string(), "ModB".to_string()]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_instances_does_not_duplicate_named_instance_roots() {
    let temp = TempDir::new().unwrap();
    create_test_module(
        temp.path(),
        "ModA",
        r"
            ---- MODULE ModA ----
            Foo == TRUE
            ====
        ",
    );
    create_test_module(
        temp.path(),
        "Main",
        r"
            ---- MODULE Main ----
            I == INSTANCE ModA
            Op == TRUE
            ====
        ",
    );

    let main_file = temp.path().join("Main.tla");
    let mut loader = ModuleLoader::new(&main_file);
    let _ = loader.load("Main").unwrap();
    let main = loader.get("Main").unwrap().module.clone();
    let instances = loader.load_instances(&main).unwrap();
    assert_eq!(instances, vec!["ModA".to_string()]);
}
