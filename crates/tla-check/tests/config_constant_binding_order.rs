// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use tla_check::{bind_constants_from_config, Config, ConstantValue, EvalCtx};
use tla_value::{intern_string, lookup_model_value_index};

#[cfg_attr(test, timeout(10000))]
#[test]
fn bind_constants_from_config_creates_model_values_in_config_file_order() {
    // Regression for #993: config constant binding must be deterministic and match TLC.
    //
    // TLC assigns UniqueString tokens in first-seen order while binding constants. This is
    // parity-critical for CHOOSE over SUBSET domains where the base-set normalization depends
    // on model value ordering.
    let mv_z = "mvZ_bind_config_order_993_3f3d2e";
    let mv_a = "mvA_bind_config_order_993_3f3d2e";

    let mv_z_arc = intern_string(mv_z);
    let mv_a_arc = intern_string(mv_a);
    assert_eq!(lookup_model_value_index(&mv_z_arc), None);
    assert_eq!(lookup_model_value_index(&mv_a_arc), None);

    let cfg = format!("CONSTANTS\n  {mv_z} <- [ model value ]\n  {mv_a} <- [ model value ]\n");
    let config = Config::parse(&cfg).expect("parse config");
    assert_eq!(
        config.constants_order,
        vec![mv_z.to_string(), mv_a.to_string()]
    );

    let mut ctx = EvalCtx::new();
    bind_constants_from_config(&mut ctx, &config).expect("bind constants");

    // TLC orders model values by UniqueString token (first-seen) order; for config-defined
    // model values that should match the config-file binding order.
    let z_idx = lookup_model_value_index(&mv_z_arc).expect("mv_z registered");
    let a_idx = lookup_model_value_index(&mv_a_arc).expect("mv_a registered");
    assert!(
        z_idx < a_idx,
        "expected mv_z before mv_a: {z_idx} < {a_idx}"
    );
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn bind_constants_from_config_falls_back_to_lexical_order_when_order_is_missing() {
    // Determinism fallback: when a Config is constructed programmatically (no parse-time order
    // capture), bind in lexicographic order.
    let mv_z = "mvZ_bind_cfg_fallback_993_7f93e2";
    let mv_a = "mvA_bind_cfg_fallback_993_7f93e2";

    let mv_z_arc = intern_string(mv_z);
    let mv_a_arc = intern_string(mv_a);
    assert_eq!(lookup_model_value_index(&mv_z_arc), None);
    assert_eq!(lookup_model_value_index(&mv_a_arc), None);

    let mut config = Config::new();
    config
        .constants
        .insert(mv_z.to_string(), ConstantValue::ModelValue);
    config
        .constants
        .insert(mv_a.to_string(), ConstantValue::ModelValue);
    assert!(config.constants_order.is_empty());

    let mut ctx = EvalCtx::new();
    bind_constants_from_config(&mut ctx, &config).expect("bind constants");

    let z_idx = lookup_model_value_index(&mv_z_arc).expect("mv_z registered");
    let a_idx = lookup_model_value_index(&mv_a_arc).expect("mv_a registered");
    assert!(
        a_idx < z_idx,
        "expected mv_a before mv_z: {a_idx} < {z_idx}"
    );
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn bind_constants_from_config_module_assignment_model_value_order_is_deterministic() {
    // Regression hardening for #1005: module-scoped CONSTANT assignments can also introduce
    // model values. Bind them deterministically so model-value registration is stable.
    let mv_z = "mvZ_bind_cfg_module_asg_993_8b2c86";
    let mv_a = "mvA_bind_cfg_module_asg_993_8b2c86";

    let mv_z_arc = intern_string(mv_z);
    let mv_a_arc = intern_string(mv_a);
    assert_eq!(lookup_model_value_index(&mv_z_arc), None);
    assert_eq!(lookup_model_value_index(&mv_a_arc), None);

    // Intentionally place ZMod before AMod in the config file. The binder should still
    // visit module assignments deterministically (lexical by module, then lexical by lhs).
    let cfg = format!("CONSTANTS\n  X = 1\n  Y = [ZMod] {mv_z}\n  Z = [AMod] {mv_a}\n");
    let config = Config::parse(&cfg).expect("parse config");

    let mut ctx = EvalCtx::new();
    bind_constants_from_config(&mut ctx, &config).expect("bind constants");

    let z_idx = lookup_model_value_index(&mv_z_arc).expect("mv_z registered");
    let a_idx = lookup_model_value_index(&mv_a_arc).expect("mv_a registered");
    assert!(
        a_idx < z_idx,
        "expected mv_a before mv_z: {a_idx} < {z_idx}"
    );
}
