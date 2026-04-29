// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::test_support::parse_module;

fn parse_op_names(raw: &str) -> FxHashSet<String> {
    raw.split(',')
        .map(str::trim)
        .filter(|name| !name.is_empty())
        .map(ToOwned::to_owned)
        .collect()
}

#[test]
fn test_clone_modules_for_selected_eval_requires_selected_operator() {
    let module = parse_module(
        "\
---- MODULE TirParitySelection ----
VARIABLE x
Live == []<>(x = 1)
TypeOK == x \\in {0, 1}
====",
    );
    let parity = TirParityState {
        mode: TirMode::Eval,
        select_all: false,
        selected_ops: parse_op_names("Live"),
        root: module,
        deps: Vec::new(),
        shared_caches: TirProgramCaches::new(),
        partial_eval_env: None,
    };

    assert!(
        parity.clone_modules_for_selected_eval("Live").is_some(),
        "selected liveness property should enable TIR module cloning"
    );
    assert!(
        parity.clone_modules_for_selected_eval("TypeOK").is_none(),
        "non-selected operators must not activate liveness TIR"
    );
}

#[test]
fn test_make_tir_program_for_selected_eval_uses_selected_operator_name() {
    let module = parse_module(
        "\
---- MODULE TirParitySelection ----
VARIABLE x
Boot == x = 0
Step == x' = x
Safe == x \\in {0}
====",
    );
    let parity = TirParityState {
        mode: TirMode::Eval,
        select_all: false,
        selected_ops: parse_op_names("Boot,Step,Safe"),
        root: module,
        deps: Vec::new(),
        shared_caches: TirProgramCaches::new(),
        partial_eval_env: None,
    };

    assert!(parity.make_tir_program_for_selected_eval("Boot").is_some());
    assert!(parity.make_tir_program_for_selected_eval("Step").is_some());
    assert!(parity.make_tir_program_for_selected_eval("Safe").is_some());
    assert!(parity.make_tir_program_for_selected_eval("Init").is_none());
    assert!(parity.make_tir_program_for_selected_eval("Next").is_none());
    assert!(parity
        .make_tir_program_for_selected_eval("TypeOK")
        .is_none());
}

#[test]
fn test_select_all_routes_every_operator_through_tir() {
    let module = parse_module(
        "\
---- MODULE TirAllMode ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TypeOK == x \\in 0..10
====",
    );
    let parity = TirParityState {
        mode: TirMode::Eval,
        select_all: true,
        selected_ops: FxHashSet::default(),
        root: module,
        deps: Vec::new(),
        shared_caches: TirProgramCaches::new(),
        partial_eval_env: None,
    };

    assert!(parity.is_selected("Init"), "all mode: Init selected");
    assert!(parity.is_selected("Next"), "all mode: Next selected");
    assert!(parity.is_selected("TypeOK"), "all mode: TypeOK selected");
    assert!(
        parity.is_selected("AnyOp"),
        "all mode: arbitrary names selected"
    );
    assert!(parity.is_eval_mode(), "all mode should be Eval");
    assert!(
        parity.make_tir_program_for_selected_eval("Init").is_some(),
        "all mode: TIR program created for Init"
    );
    assert!(
        parity.clone_modules_for_selected_eval("TypeOK").is_some(),
        "all mode: modules cloned for TypeOK"
    );
    assert!(
        parity.selected_named_op_uses_tir_eval_name("Next", "Next"),
        "plain Next operators should keep the real TIR path"
    );
}

#[test]
fn test_binding_form_next_counts_as_real_tir_eval_when_lowerable() {
    let module = parse_module(
        "\
---- MODULE TirBindingFallback ----
VARIABLE x
Next == x' = [i \\in {0, 1} |-> i][x]
====
",
    );
    let parity = TirParityState {
        mode: TirMode::Eval,
        select_all: true,
        selected_ops: FxHashSet::default(),
        root: module,
        deps: Vec::new(),
        shared_caches: TirProgramCaches::new(),
        partial_eval_env: None,
    };

    assert!(
        parity.selected_named_op_uses_tir_eval_name("Next", "Next"),
        "lowerable binding-form Next bodies should use the real TIR eval path"
    );
    assert!(
        parity.make_tir_program_for_selected_eval("Next").is_some(),
        "selected Next should allocate a TIR program once lowering succeeds"
    );
    assert!(
        parity
            .make_tir_program_for_selected_leaf_eval_name("Next", "Next")
            .is_some(),
        "leaf-eval callers should still receive a TIR program for per-expression fallback"
    );
}

#[test]
fn test_make_tir_program_for_selected_leaf_eval_name_matches_raw_or_resolved_name() {
    let module = parse_module(
        "\
---- MODULE TirLeafSelectionNameRouting ----
VARIABLE x
ResolvedInit == x = 0
====",
    );
    let parity = TirParityState {
        mode: TirMode::Eval,
        select_all: false,
        selected_ops: parse_op_names("Init"),
        root: module,
        deps: Vec::new(),
        shared_caches: TirProgramCaches::new(),
        partial_eval_env: None,
    };

    let program = parity
        .make_tir_program_for_selected_leaf_eval_name("Init", "ResolvedInit")
        .expect("raw INIT selection should still activate resolved leaf TIR");
    let expected_labels = vec!["Init".to_string(), "ResolvedInit".to_string()];
    assert_eq!(
        program.probe_labels(),
        expected_labels.as_slice(),
        "leaf-eval routing should preserve both raw and resolved labels for probe diagnostics"
    );
}
