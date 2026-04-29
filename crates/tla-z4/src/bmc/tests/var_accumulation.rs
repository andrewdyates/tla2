// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for variable accumulation prevention across cooperative seeds.
//!
//! When the BMC translator is reused across multiple seeds in the cooperative
//! engine, Skolem constants from quantifier expansion and CHOOSE translation
//! are inserted into the translator's `vars` map. Without cleanup, these
//! accumulate across seeds. The `clear_temporary_vars` method evicts them.
//!
//! Part of #4006.

use super::*;

/// Verify that `clear_temporary_vars` removes Skolem entries while
/// preserving base state variables.
#[test]
fn test_clear_temporary_vars_preserves_base_vars() {
    let mut translator = BmcTranslator::new(3).unwrap();
    translator
        .declare_var("x", TlaSort::Int)
        .expect("declare x");
    translator
        .declare_var("y", TlaSort::Bool)
        .expect("declare y");

    assert_eq!(translator.total_var_count(), 2);
    assert_eq!(translator.temporary_var_count(), 0);

    // Simulate a Skolem constant being inserted (this is what
    // skolemize_bmc_exists_range and friends do internally).
    translator.vars.insert(
        "__bmc_sk_z_0".to_string(),
        BmcVarInfo {
            sort: TlaSort::Int,
            terms: vec![],
        },
    );
    translator.vars.insert(
        "__bmc_sk_w_1".to_string(),
        BmcVarInfo {
            sort: TlaSort::Int,
            terms: vec![],
        },
    );

    assert_eq!(translator.total_var_count(), 4);
    assert_eq!(translator.temporary_var_count(), 2);

    // Clear temporaries.
    translator.clear_temporary_vars();

    assert_eq!(
        translator.total_var_count(),
        2,
        "only base vars should remain"
    );
    assert_eq!(translator.temporary_var_count(), 0);
    assert!(translator.vars.contains_key("x"));
    assert!(translator.vars.contains_key("y"));
    assert!(!translator.vars.contains_key("__bmc_sk_z_0"));
    assert!(!translator.vars.contains_key("__bmc_sk_w_1"));
}

/// Verify that `clear_temporary_vars` is a no-op when no temporaries exist.
#[test]
fn test_clear_temporary_vars_noop_when_clean() {
    let mut translator = BmcTranslator::new(2).unwrap();
    translator
        .declare_var("count", TlaSort::Int)
        .expect("declare count");

    assert_eq!(translator.total_var_count(), 1);
    assert_eq!(translator.temporary_var_count(), 0);

    translator.clear_temporary_vars();

    assert_eq!(translator.total_var_count(), 1);
    assert!(translator.vars.contains_key("count"));
}

/// Verify that push/pop + clear_temporary_vars keeps the translator clean
/// across multiple simulated seeds.
#[test]
fn test_multi_seed_no_accumulation() {
    let mut translator = BmcTranslator::new(3).unwrap();
    translator
        .declare_var("count", TlaSort::Int)
        .expect("declare count");

    assert_eq!(translator.total_var_count(), 1);

    // Simulate 10 seeds, each injecting temporary variables.
    for seed_id in 0..10 {
        translator.push_scope().expect("push");

        // Simulate Skolem constant injection (as quantifier translation does).
        let sk_name = format!("__bmc_sk_x_{seed_id}");
        translator.vars.insert(
            sk_name,
            BmcVarInfo {
                sort: TlaSort::Int,
                terms: vec![],
            },
        );

        assert_eq!(
            translator.temporary_var_count(),
            1,
            "seed {seed_id}: should have 1 temporary var"
        );

        translator.pop_scope().expect("pop");
        translator.clear_temporary_vars();

        assert_eq!(
            translator.total_var_count(),
            1,
            "seed {seed_id}: should be back to 1 base var after cleanup"
        );
        assert_eq!(
            translator.temporary_var_count(),
            0,
            "seed {seed_id}: should have 0 temporaries after cleanup"
        );
    }
}

/// Verify that without `clear_temporary_vars`, temporary variables accumulate.
/// This documents the bug that #4006 fixes.
#[test]
fn test_without_clear_vars_accumulate() {
    let mut translator = BmcTranslator::new(3).unwrap();
    translator
        .declare_var("count", TlaSort::Int)
        .expect("declare count");

    // Simulate 10 seeds WITHOUT calling clear_temporary_vars.
    for seed_id in 0..10 {
        translator.push_scope().expect("push");

        let sk_name = format!("__bmc_sk_x_{seed_id}");
        translator.vars.insert(
            sk_name,
            BmcVarInfo {
                sort: TlaSort::Int,
                terms: vec![],
            },
        );

        translator.pop_scope().expect("pop");
        // Intentionally NOT calling clear_temporary_vars here.
    }

    // Without cleanup, all 10 Skolem constants remain.
    assert_eq!(
        translator.total_var_count(),
        11,
        "without cleanup, 1 base + 10 Skolem = 11 total"
    );
    assert_eq!(
        translator.temporary_var_count(),
        10,
        "without cleanup, 10 temporary vars accumulated"
    );

    // A single clear fixes the accumulation.
    translator.clear_temporary_vars();
    assert_eq!(translator.total_var_count(), 1);
    assert_eq!(translator.temporary_var_count(), 0);
}

/// Verify that `declare_var` with compound types (Function, Sequence) also
/// registers as base variables.
#[test]
fn test_compound_type_base_vars_preserved() {
    let mut translator = BmcTranslator::new_with_arrays(2).unwrap();
    translator
        .declare_var("x", TlaSort::Int)
        .expect("declare x");
    translator
        .declare_var(
            "s",
            TlaSort::Set {
                element_sort: Box::new(TlaSort::Int),
            },
        )
        .expect("declare s");

    // x goes into vars, s also goes into vars (set-typed).
    // Note: func_vars, seq_vars etc. are separate maps and not affected
    // by clear_temporary_vars. The base_var_names tracking is specifically
    // for the `vars` HashMap which is where Skolem constants accumulate.
    let base_count = translator.total_var_count();
    assert!(base_count >= 2, "should have at least x and s");

    // Add a fake Skolem.
    translator.vars.insert(
        "__bmc_choose_tmp_0".to_string(),
        BmcVarInfo {
            sort: TlaSort::Int,
            terms: vec![],
        },
    );

    assert_eq!(translator.temporary_var_count(), 1);

    translator.clear_temporary_vars();

    assert_eq!(translator.total_var_count(), base_count);
    assert_eq!(translator.temporary_var_count(), 0);
}
