// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Config-backed Disruptor_MPMC regression tests for invariant checking.

use super::*;

#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn test_check_successor_invariant_tir_eval_real_disruptor_mpmc_nodataraces_counterexample() {
    let (module, checker_modules, config) = load_real_disruptor_mpmc_modules();
    let checker_module_refs: Vec<_> = checker_modules.iter().collect();
    let state = real_disruptor_mpmc_counterexample_state();

    let mut baseline = ModelChecker::new_with_extends(&module, &checker_module_refs, &config);
    baseline.sync_tlc_config("bfs");
    crate::constants::bind_constants_from_config(&mut baseline.ctx, &config)
        .expect("Disruptor_MPMC constants should bind");
    crate::check::model_checker::precompute_constant_operators(&mut baseline.ctx);
    crate::check::model_checker::promote_env_constants_to_precomputed(&mut baseline.ctx);
    let registry = baseline.ctx.var_registry().clone();
    let array_state = ArrayState::from_state(&state, &registry);

    assert!(
        matches!(
            baseline.check_successor_invariant(Fingerprint(0), &array_state, Fingerprint(1), 7),
            crate::checker_ops::InvariantOutcome::Ok
        ),
        "AST invariant path should accept the real Disruptor_MPMC counterexample state"
    );

    let mut tir = ModelChecker::new_with_extends(&module, &checker_module_refs, &config);
    tir.sync_tlc_config("bfs");
    crate::constants::bind_constants_from_config(&mut tir.ctx, &config)
        .expect("Disruptor_MPMC constants should bind");
    crate::check::model_checker::precompute_constant_operators(&mut tir.ctx);
    crate::check::model_checker::promote_env_constants_to_precomputed(&mut tir.ctx);
    tir.tir_parity = Some(
        super::super::super::super::tir_parity::TirParityState::test_eval_selected(
            module.clone(),
            checker_modules.clone(),
            ["NoDataRaces"],
        ),
    );

    assert!(
        matches!(
            tir.check_successor_invariant(Fingerprint(0), &array_state, Fingerprint(1), 7),
            crate::checker_ops::InvariantOutcome::Ok
        ),
        "TIR invariant path should match the AST result on the real Disruptor_MPMC counterexample state"
    );
}

#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn test_check_successor_invariant_tir_eval_real_disruptor_mpmc_nodataraces_trace_transition() {
    let (module, checker_modules, config) = load_real_disruptor_mpmc_modules();
    let checker_module_refs: Vec<_> = checker_modules.iter().collect();
    let state7 = real_disruptor_mpmc_trace_state7();
    let state8 = real_disruptor_mpmc_counterexample_state();

    let mut baseline = ModelChecker::new_with_extends(&module, &checker_module_refs, &config);
    baseline.sync_tlc_config("bfs");
    crate::constants::bind_constants_from_config(&mut baseline.ctx, &config)
        .expect("Disruptor_MPMC constants should bind");
    crate::check::model_checker::precompute_constant_operators(&mut baseline.ctx);
    crate::check::model_checker::promote_env_constants_to_precomputed(&mut baseline.ctx);
    let registry = baseline.ctx.var_registry().clone();
    let array_state7 = ArrayState::from_state(&state7, &registry);
    let array_state8 = ArrayState::from_state(&state8, &registry);

    assert!(
        matches!(
            baseline.check_successor_invariant(Fingerprint(0), &array_state7, Fingerprint(1), 6),
            crate::checker_ops::InvariantOutcome::Ok
        ),
        "AST invariant path should accept Disruptor_MPMC trace state 7"
    );
    assert!(
        matches!(
            baseline.check_successor_invariant(Fingerprint(1), &array_state8, Fingerprint(2), 7),
            crate::checker_ops::InvariantOutcome::Ok
        ),
        "AST invariant path should accept Disruptor_MPMC trace state 8 after state 7"
    );

    let mut tir = ModelChecker::new_with_extends(&module, &checker_module_refs, &config);
    tir.sync_tlc_config("bfs");
    crate::constants::bind_constants_from_config(&mut tir.ctx, &config)
        .expect("Disruptor_MPMC constants should bind");
    crate::check::model_checker::precompute_constant_operators(&mut tir.ctx);
    crate::check::model_checker::promote_env_constants_to_precomputed(&mut tir.ctx);
    tir.tir_parity = Some(
        super::super::super::super::tir_parity::TirParityState::test_eval_selected(
            module.clone(),
            checker_modules.clone(),
            ["NoDataRaces"],
        ),
    );

    assert!(
        matches!(
            tir.check_successor_invariant(Fingerprint(0), &array_state7, Fingerprint(1), 6),
            crate::checker_ops::InvariantOutcome::Ok
        ),
        "TIR invariant path should accept Disruptor_MPMC trace state 7"
    );
    assert!(
        matches!(
            tir.check_successor_invariant(Fingerprint(1), &array_state8, Fingerprint(2), 7),
            crate::checker_ops::InvariantOutcome::Ok
        ),
        "TIR invariant path should accept Disruptor_MPMC trace state 8 after state 7"
    );
}

#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn test_check_real_disruptor_mpmc_liveliness_cfg_passes_under_default_tir_eval() {
    let (module, checker_modules, config, resolved) =
        load_real_disruptor_mpmc_modules_with_cfg("Disruptor_MPMC_liveliness.cfg");
    let checker_module_refs: Vec<_> = checker_modules.iter().collect();

    let mut checker = ModelChecker::new_with_extends(&module, &checker_module_refs, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);
    checker.set_fairness(resolved.fairness);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 14365,
                "Disruptor_MPMC_liveliness should match the TLC baseline state count"
            );
        }
        other => {
            panic!("expected Disruptor_MPMC_liveliness to pass under default TIR, got {other:?}")
        }
    }
}

/// Part of #3391: verify the standard Disruptor_MPMC config (3 readers)
/// also passes under default TIR eval. This narrows whether the false positive
/// is specific to the liveliness config (2 readers) or systematic.
#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn test_check_real_disruptor_mpmc_standard_cfg_passes_under_default_tir_eval() {
    let (module, checker_modules, config, resolved) =
        load_real_disruptor_mpmc_modules_with_cfg("Disruptor_MPMC.cfg");
    let checker_module_refs: Vec<_> = checker_modules.iter().collect();

    let mut checker = ModelChecker::new_with_extends(&module, &checker_module_refs, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);
    checker.set_fairness(resolved.fairness);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 112929,
                "Disruptor_MPMC standard should match the TLC baseline state count"
            );
        }
        other => {
            panic!("expected Disruptor_MPMC standard to pass under default TIR, got {other:?}")
        }
    }
}
