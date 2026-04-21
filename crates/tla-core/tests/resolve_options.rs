// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::{Mutex, OnceLock};

use tla_core::{
    lower, parse_to_syntax_tree, resolve_with_options, FileId, ResolveErrorKind, ResolveOptions,
};

fn resolve_options_test_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn resolve_can_ignore_tlaps_proof_scripts_for_model_checking() {
    let _lock = resolve_options_test_lock().lock().unwrap();

    let src = r"
---- MODULE Test ----
EXTENDS TLAPS

THEOREM T == TRUE
<1>1. HAVE self = 1
  OBVIOUS
<1>. QED
====
";

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("lower produced no module");

    let with_proofs = resolve_with_options(&module, ResolveOptions::default());
    assert!(
        with_proofs.errors.iter().any(|e| matches!(
            &e.kind,
            ResolveErrorKind::Undefined { name } if name == "self"
        )),
        "expected undefined `self` in proof resolution; errors: {:?}",
        with_proofs.errors
    );

    let without_proofs = resolve_with_options(&module, ResolveOptions::model_checking());
    assert!(
        without_proofs.is_ok(),
        "expected proof-ignored resolve to succeed; errors: {:?}",
        without_proofs.errors
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn module_loader_finds_repo_local_tla_library_without_repo_cwd() {
    let _lock = resolve_options_test_lock().lock().unwrap();

    struct CwdGuard(std::path::PathBuf);

    impl Drop for CwdGuard {
        fn drop(&mut self) {
            let _ = std::env::set_current_dir(&self.0);
        }
    }

    let _guard = CwdGuard(std::env::current_dir().expect("current dir"));

    let tmp = tempfile::tempdir().expect("tempdir");
    std::env::set_current_dir(tmp.path()).expect("set cwd");

    let main_file = tmp.path().join("Main.tla");
    let main_src = concat!(
        "------------------------- MODULE Main -------------------------\n",
        "EXTENDS FunctionTheorems\n",
        "=============================================================\n",
    );
    std::fs::write(&main_file, main_src).expect("write Main.tla");

    let mut loader = tla_core::ModuleLoader::new(&main_file);
    let loaded = loader
        .load("FunctionTheorems")
        .expect("load FunctionTheorems from repo-local library");

    assert_eq!(
        loaded.path.file_name().and_then(|n| n.to_str()),
        Some("FunctionTheorems.tla")
    );
}
