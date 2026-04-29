// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::json_output::JsonValue;
use crate::state::State;
use crate::value::Value;
use crate::EvalCtx;
use std::collections::HashMap;
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn load_spec(src: &str) -> (EvalCtx, tla_core::ast::Module) {
    let tree = parse_to_syntax_tree(src);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("lowered module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    (ctx, module)
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_action_label_satisfied() {
    let src = r#"
---- MODULE Test ----
VARIABLE x

Inc(a) == x' = x + a

Next == Inc(1) \/ Inc(2)
====
"#;

    let (mut ctx, _module) = load_spec(src);

    let toml = r#"
[[actions]]
label = "Increment"
operator = "Inc"
params = ["a"]
"#;
    let mapping =
        ActionLabelMappingConfig::from_toml_str("test".to_string(), toml).expect("parse config");

    let state = State::from_pairs([("x", Value::int(0))]);
    let next_state = State::from_pairs([("x", Value::int(1))]);

    let mut params = HashMap::new();
    params.insert("a".to_string(), JsonValue::Int(1));

    let result = validate_action_label(
        &mut ctx,
        &mapping,
        &state,
        &next_state,
        "Increment",
        &params,
    )
    .expect("validation should succeed");
    assert_eq!(result, ActionLabelValidationResult::Satisfied);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_action_label_not_satisfied() {
    let src = r#"
---- MODULE Test ----
VARIABLE x

Inc(a) == x' = x + a

Next == Inc(1) \/ Inc(2)
====
"#;

    let (mut ctx, _module) = load_spec(src);

    let toml = r#"
[[actions]]
label = "Increment"
operator = "Inc"
params = ["a"]
"#;
    let mapping =
        ActionLabelMappingConfig::from_toml_str("test".to_string(), toml).expect("parse config");

    let state = State::from_pairs([("x", Value::int(0))]);
    let next_state = State::from_pairs([("x", Value::int(1))]);

    let mut params = HashMap::new();
    params.insert("a".to_string(), JsonValue::Int(2));

    let result = validate_action_label(
        &mut ctx,
        &mapping,
        &state,
        &next_state,
        "Increment",
        &params,
    )
    .expect("validation should succeed");
    assert_eq!(result, ActionLabelValidationResult::NotSatisfied);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_action_label_unknown_label() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;

    let (mut ctx, _module) = load_spec(src);

    let toml = r#"
[[actions]]
label = "Step"
operator = "Next"
params = []
"#;
    let mapping =
        ActionLabelMappingConfig::from_toml_str("test".to_string(), toml).expect("parse config");

    let state = State::from_pairs([("x", Value::int(0))]);
    let next_state = State::from_pairs([("x", Value::int(1))]);
    let params = HashMap::new();

    let result = validate_action_label(&mut ctx, &mapping, &state, &next_state, "Unknown", &params);
    assert!(matches!(
        result,
        Err(ActionLabelValidationError::UnknownLabel { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_action_label_param_mismatch() {
    let src = r#"
---- MODULE Test ----
VARIABLE x

Inc(a) == x' = x + a

Next == Inc(1)
====
"#;

    let (mut ctx, _module) = load_spec(src);

    let toml = r#"
[[actions]]
label = "Increment"
operator = "Inc"
params = ["a"]
"#;
    let mapping =
        ActionLabelMappingConfig::from_toml_str("test".to_string(), toml).expect("parse config");

    let state = State::from_pairs([("x", Value::int(0))]);
    let next_state = State::from_pairs([("x", Value::int(1))]);

    let mut params = HashMap::new();
    params.insert("b".to_string(), JsonValue::Int(1));

    let result = validate_action_label(
        &mut ctx,
        &mapping,
        &state,
        &next_state,
        "Increment",
        &params,
    );
    assert!(matches!(
        result,
        Err(ActionLabelValidationError::ParamMismatch { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_action_label_no_params() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;

    let (mut ctx, _module) = load_spec(src);

    let toml = r#"
[[actions]]
label = "Step"
operator = "Next"
params = []
"#;
    let mapping =
        ActionLabelMappingConfig::from_toml_str("test".to_string(), toml).expect("parse config");

    let state = State::from_pairs([("x", Value::int(0))]);
    let next_state = State::from_pairs([("x", Value::int(1))]);
    let params = HashMap::new();

    let result = validate_action_label(&mut ctx, &mapping, &state, &next_state, "Step", &params)
        .expect("validation should succeed");
    assert_eq!(result, ActionLabelValidationResult::Satisfied);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_action_label_stutter_not_allowed() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1 \/ x' = x  \* Can stutter
====
"#;

    let (mut ctx, _module) = load_spec(src);

    let toml = r#"
[[actions]]
label = "Step"
operator = "Next"
params = []
allow_stutter = false
"#;
    let mapping =
        ActionLabelMappingConfig::from_toml_str("test".to_string(), toml).expect("parse config");

    let state = State::from_pairs([("x", Value::int(5))]);
    let next_state = State::from_pairs([("x", Value::int(5))]);
    let params = HashMap::new();

    let result = validate_action_label(&mut ctx, &mapping, &state, &next_state, "Step", &params);
    assert!(matches!(
        result,
        Err(ActionLabelValidationError::StutterNotAllowed { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_action_label_stutter_allowed() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1 \/ x' = x  \* Can stutter
====
"#;

    let (mut ctx, _module) = load_spec(src);

    let toml = r#"
[[actions]]
label = "Step"
operator = "Next"
params = []
allow_stutter = true
"#;
    let mapping =
        ActionLabelMappingConfig::from_toml_str("test".to_string(), toml).expect("parse config");

    let state = State::from_pairs([("x", Value::int(5))]);
    let next_state = State::from_pairs([("x", Value::int(5))]);
    let params = HashMap::new();

    let result = validate_action_label(&mut ctx, &mapping, &state, &next_state, "Step", &params)
        .expect("validation should succeed");
    assert_eq!(result, ActionLabelValidationResult::Satisfied);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_action_label_module_ref() {
    let inst_src = r#"
---- MODULE Inst ----
VARIABLE x

Inc(a) == x' = x + a
====
"#;
    let main_src = r#"
---- MODULE Test ----
VARIABLE x

I == INSTANCE Inst

Next == I!Inc(1) \/ I!Inc(2)
====
"#;

    let inst_tree = parse_to_syntax_tree(inst_src);
    let inst_lowered = lower(FileId(0), &inst_tree);
    assert!(inst_lowered.errors.is_empty());
    let inst_module = inst_lowered.module.expect("inst module");

    let main_tree = parse_to_syntax_tree(main_src);
    let main_lowered = lower(FileId(1), &main_tree);
    assert!(main_lowered.errors.is_empty());
    let main_module = main_lowered.module.expect("main module");

    let mut ctx = EvalCtx::new();
    ctx.load_instance_module("Inst".to_string(), &inst_module);
    ctx.load_module(&main_module);

    let toml = r#"
[[actions]]
label = "Increment"
operator = "I!Inc"
params = ["a"]
"#;
    let mapping =
        ActionLabelMappingConfig::from_toml_str("test".to_string(), toml).expect("parse config");

    let state = State::from_pairs([("x", Value::int(0))]);
    let next_state = State::from_pairs([("x", Value::int(1))]);

    let mut params = HashMap::new();
    params.insert("a".to_string(), JsonValue::Int(1));

    let result = validate_action_label(
        &mut ctx,
        &mapping,
        &state,
        &next_state,
        "Increment",
        &params,
    )
    .expect("validation should succeed");
    assert_eq!(result, ActionLabelValidationResult::Satisfied);

    let mut wrong_params = HashMap::new();
    wrong_params.insert("a".to_string(), JsonValue::Int(2));

    let result2 = validate_action_label(
        &mut ctx,
        &mapping,
        &state,
        &next_state,
        "Increment",
        &wrong_params,
    )
    .expect("validation should succeed");
    assert_eq!(result2, ActionLabelValidationResult::NotSatisfied);
}
